use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use std::time::{SystemTime, UNIX_EPOCH};

use rand::rngs::OsRng;
use rand::Rng;

static H : usize = 14;
static W : usize = 14;
static BLUR_H : usize = 6;
static BLUR_W : usize = 6;

fn print_time_since(last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!("{:?} - time since last check: {:?}", tag, (now - last) as f32 / 60000.0); 
    return now;
}

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let mut rng = OsRng;

    let mut w_r_vals = Vec::new();
    let mut x_r_vals = Vec::new();

    for _ in 0..H {
        let mut r_row = Vec::new();
        for _ in 0..W {
            r_row.push(rng.gen_range(0..256) as usize);
        }
        w_r_vals.push(r_row);
    }

    for i in 0..H {
        let mut r_row = Vec::new();
        for j in 0..W {

            if i > 0 && i < 1 + BLUR_H && j > 0 && j < 1 + BLUR_W {
                // in blur region
                let sum_r = w_r_vals[i-1][j-1] + w_r_vals[i-1][j] + w_r_vals[i-1][j+1]
                            + w_r_vals[i][j-1] + w_r_vals[i][j] + w_r_vals[i][j+1]
                            + w_r_vals[i+1][j-1] + w_r_vals[i+1][j] + w_r_vals[i+1][j+1]; 

                let blur_r = (sum_r as f64 / 9.0).round() as usize;
                r_row.push(blur_r);
            }
            else {
                r_row.push(w_r_vals[i][j]);
            }
        }
        x_r_vals.push(r_row);
    }    

    // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;
           
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut w_r_targets = Vec::new();
    for _ in 0..H {
        let mut w_r_target_row = Vec::new();
        for _ in 0..W {
            let w_r = builder.add_virtual_target();
            w_r_target_row.push(w_r);
        }  
        w_r_targets.push(w_r_target_row);       
    }

    let mut x_r_targets = Vec::new();
    for i in 0..H {
        let mut x_r_target_row = Vec::new();
        for j in 0..W {
            if i > 0 && i < 1 + BLUR_H && j > 0 && j < 1 + BLUR_W {
                // in blur region
                let mut all_r = Vec::new();

                all_r.push(w_r_targets[i-1][j-1]);
                all_r.push(w_r_targets[i-1][j]);
                all_r.push(w_r_targets[i-1][j+1]);
                all_r.push(w_r_targets[i][j-1]);
                all_r.push(w_r_targets[i][j]);
                all_r.push(w_r_targets[i][j+1]);
                all_r.push(w_r_targets[i+1][j-1]);
                all_r.push(w_r_targets[i+1][j]);
                all_r.push(w_r_targets[i+1][j+1]);
                

                let s_r = builder.add_many(all_r);

                // add 4 this so that remainder moves from value in [-4,4] to value in [0,8]
                let s_r_shift = builder.add_const(s_r, F::from_canonical_u32(4));
                
                let x_r = builder.add_virtual_target();
                x_r_target_row.push(x_r);
                let x_r_times_9 = builder.mul_const(F::from_canonical_u32(9), x_r);

                let rem_r = builder.sub(s_r_shift, x_r_times_9);

                // To check that rem \in [0, 8], we must check that rem < 2^4 and that
                // rem + 7 < 2^4
                builder.range_check(rem_r, 4);
                let rem_r_plus_7 = builder.add_const(rem_r, F::from_canonical_u32(7));
                builder.range_check(rem_r_plus_7, 4);

            }
            else {
                builder.register_public_input(w_r_targets[i][j]);
            } 
        }
        if x_r_target_row.len() > 0 {
             x_r_targets.push(x_r_target_row);
        }
    }
    
    let data = builder.build::<C>();
    last = print_time_since(last, "setup done"); 

    let mut pw = PartialWitness::new();

    for i in 0..H {
        for j in 0..W {
            pw.set_target(w_r_targets[i][j], F::from_canonical_u32(w_r_vals[i][j] as u32));
       }
    }

    for i in 0..BLUR_H {
        for j in 0..BLUR_W {
            pw.set_target(x_r_targets[i][j], F::from_canonical_u32(x_r_vals[i+1][j+1] as u32));
        }
    }


    let proof = data.prove(pw)?;
    last = print_time_since(last, "proof done");

    let mut ctr = 0;
    for i in 0..H {
        for j in 0..W {
            if !(i > 0 && i < 1 + BLUR_H && j > 0 && j < 1 + BLUR_W) {
                assert!(x_r_vals[i][j] as u64 == proof.public_inputs[ctr].0);
                ctr += 1;
            }

        }
    }

    let res = data.verify(proof);
    let _ = res.unwrap();

    _ = print_time_since(last, "verify done"); 

    Ok(())
}
