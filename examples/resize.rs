use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use std::time::{SystemTime, UNIX_EPOCH};

use rand::rngs::OsRng;
use rand::Rng;

static H_ORIG : usize = 10;
static W_ORIG : usize = 10;
static H_NEW : usize = 6;
static W_NEW : usize = 6;

/*static H_ORIG : usize = 6632;
static W_ORIG : usize = 4976;
static H_NEW : usize = 2048;
static W_NEW : usize = 1365;*/


fn print_time_since(last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!("{:?} - time since last check: {:?}", tag, (now - last) as f32 / 60000.0); 
    return now;
}

fn get_positions(i: usize, j: usize) -> (usize, usize, usize, usize) {
    let x_l = (W_ORIG - 1) * j / (W_NEW - 1);
    let y_l = (H_ORIG - 1) * i / (H_NEW - 1);

    let x_h = if x_l * (W_NEW - 1) == (W_ORIG - 1) * j { x_l } else { x_l + 1 };
    let y_h = if y_l * (H_NEW - 1) == (H_ORIG - 1) * i { y_l } else { y_l + 1 };

    return (x_l, y_l, x_h, y_h);
}

fn get_ratios(i: usize, j: usize) -> (usize, usize) {
    let x_ratio_weighted = ((W_ORIG - 1) * j) - (W_NEW - 1) * ((W_ORIG - 1) * j / (W_NEW - 1));
    let y_ratio_weighted = ((H_ORIG - 1) * i) - (H_NEW - 1) * ((H_ORIG - 1) * i / (H_NEW - 1));
    return (x_ratio_weighted, y_ratio_weighted);
}

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let mut rng = OsRng;

    let mut w_r_vals = Vec::new();
    let mut w_g_vals = Vec::new();
    let mut w_b_vals = Vec::new();
    let mut x_r_vals = Vec::new();
    let mut rem_r_vals = Vec::new();

    for _ in 0..H_ORIG {
        let mut r_row = Vec::new();
        let mut g_row = Vec::new();
        let mut b_row = Vec::new();
        for _ in 0..W_ORIG {
            r_row.push(rng.gen_range(0..256) as usize);
            g_row.push(rng.gen_range(0..256) as usize);
            b_row.push(rng.gen_range(0..256) as usize);
        }
        w_r_vals.push(r_row);
        w_g_vals.push(g_row);
        w_b_vals.push(b_row);
    }

    // ONLY FOR RED VALUES....then you'll try for G and B values
    for i in 0..H_NEW {
        let mut r_row = Vec::new();
        let mut rem_r_row = Vec::new();
        for j in 0..W_NEW {
            let (x_l, y_l, x_h, y_h) = get_positions(i, j);

            let (x_ratio_weighted, y_ratio_weighted) = get_ratios(i, j);

            let a = w_r_vals[y_l][x_l];
            let b = w_r_vals[y_l][x_h];
            let c = w_r_vals[y_h][x_l];
            let d = w_r_vals[y_h][x_h];

            let s = a * (W_NEW - 1 - x_ratio_weighted) * (H_NEW - 1 - y_ratio_weighted) 
                    + b * x_ratio_weighted * (H_NEW - 1 - y_ratio_weighted) 
                    + c * y_ratio_weighted * (W_NEW - 1 - x_ratio_weighted) 
                    + d * x_ratio_weighted * y_ratio_weighted;

            let new = ((s as f64) / (((W_NEW - 1) * (H_NEW - 1)) as f64)).round() as usize;

            let r = s as i64 - (new * (W_NEW - 1) * (H_NEW - 1)) as i64;
            
            r_row.push(new);
            rem_r_row.push(r);
        }
        x_r_vals.push(r_row);
        rem_r_vals.push(rem_r_row);
    }              
      
    let mut config = CircuitConfig::standard_recursion_config();
    config.zero_knowledge = true;
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut pw = PartialWitness::new();

    let mut w_r_targets = Vec::new();

    for i in 0..H_NEW {
        for j in 0..W_NEW {
            let a = builder.add_virtual_target();
            let b = builder.add_virtual_target();
            let c = builder.add_virtual_target();
            let d = builder.add_virtual_target();
            
            w_r_targets.push(a);
            w_r_targets.push(b);
            w_r_targets.push(c);
            w_r_targets.push(d);

            let (x_ratio_weighted, y_ratio_weighted) = get_ratios(i, j);

            let mut all = Vec::new();

            let a_const = ((W_NEW - 1 - x_ratio_weighted) * (H_NEW - 1 - y_ratio_weighted)) as u32;
            let b_const = (x_ratio_weighted * (H_NEW - 1 - y_ratio_weighted)) as u32;
            let c_const = (y_ratio_weighted * (W_NEW - 1 - x_ratio_weighted)) as u32;
            let d_const = (x_ratio_weighted * y_ratio_weighted) as u32;
            all.push(builder.mul_const(F::from_canonical_u32(a_const), a));
            all.push(builder.mul_const(F::from_canonical_u32(b_const), b));
            all.push(builder.mul_const(F::from_canonical_u32(c_const), c));
            all.push(builder.mul_const(F::from_canonical_u32(d_const), d));

            let s = builder.add_many(all);
            builder.register_public_input(s);
        }         
    }
 
    // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    let data = builder.build::<C>();
    last = print_time_since(last, "setup done"); 

    for i in 0..H_NEW {
        for j in 0..W_NEW {

            let (x_l, y_l, x_h, y_h) = get_positions(i, j);

            pw.set_target(w_r_targets[4 * i * W_NEW + 4 * j], F::from_canonical_u32(w_r_vals[y_l][x_l] as u32));
            pw.set_target(w_r_targets[4 * i * W_NEW + 4 * j + 1], F::from_canonical_u32(w_r_vals[y_l][x_h] as u32));
            pw.set_target(w_r_targets[4 * i * W_NEW + 4 * j + 2], F::from_canonical_u32(w_r_vals[y_h][x_l] as u32));
            pw.set_target(w_r_targets[4 * i * W_NEW + 4 * j + 3], F::from_canonical_u32(w_r_vals[y_h][x_h] as u32));
        }
    }

    let proof = data.prove(pw)?;
    last = print_time_since(last, "proof done");

    let denom = (W_NEW - 1) * (H_NEW - 1);

    for i in 0..H_NEW {
        for j in 0..W_NEW {
            let x = (x_r_vals[i][j] * denom) as i64 + rem_r_vals[i][j];
            assert!(x as u64 == proof.public_inputs[W_NEW * i + j].0);
        }
    }

    let res = data.verify(proof);
    let _ = res.unwrap();

    _ = print_time_since(last, "verify done"); 

    Ok(())
}