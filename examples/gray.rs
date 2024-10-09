use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use std::time::{SystemTime, UNIX_EPOCH};

use rand::rngs::OsRng;
use rand::Rng;

static PIXELS : usize = 10;

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

    let mut r_vals = Vec::new();
    let mut g_vals = Vec::new();
    let mut b_vals = Vec::new();
    let mut x_vals = Vec::new();
    let mut rem_vals = Vec::new();

    for i in 0..PIXELS {
        r_vals.push(rng.gen_range(0..256) as u32);
        g_vals.push(rng.gen_range(0..256) as u32);
        b_vals.push(rng.gen_range(0..256) as u32);

        let r_f = r_vals[i] as f64;
        let g_f = g_vals[i] as f64;
        let b_f = b_vals[i] as f64;

        let x_f = 0.3 * r_f + 0.59 * g_f + 0.11 * b_f;
        x_vals.push(x_f.round() as i32);

        rem_vals.push((r_vals[i] * 30 + g_vals[i] * 59 + b_vals[i] * 11) as i32 - 100 * x_vals[i]);
    }
   
     // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    let mut config = CircuitConfig::standard_recursion_config();
    config.zero_knowledge = true;
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut pw = PartialWitness::new();

    let mut r_targets = Vec::new();
    let mut g_targets = Vec::new();
    let mut b_targets = Vec::new();

    for _ in 0..PIXELS {
        let r = builder.add_virtual_target();
        r_targets.push(r);

        let g = builder.add_virtual_target();
        g_targets.push(g);

        let b = builder.add_virtual_target();
        b_targets.push(b);

        let mut all = Vec::new();

        all.push(builder.mul_const(F::from_canonical_u32(30), r));
        all.push(builder.mul_const(F::from_canonical_u32(59), g));
        all.push(builder.mul_const(F::from_canonical_u32(11), b));

        let s = builder.add_many(all);
        builder.register_public_input(s);
    }

    let data = builder.build::<C>();
    last = print_time_since(last, "setup done"); 

    for i in 0..PIXELS {
        pw.set_target(r_targets[i], F::from_canonical_u32(r_vals[i]));
        pw.set_target(g_targets[i], F::from_canonical_u32(g_vals[i]));
        pw.set_target(b_targets[i], F::from_canonical_u32(b_vals[i]));
    }

    let proof = data.prove(pw)?;
    last = print_time_since(last, "proof done"); 

    for i in 0..PIXELS {
        assert!((proof.public_inputs[i].0) as i32 == 100 * x_vals[i] + rem_vals[i])
    }

    let res = data.verify(proof);
    let _ = res.unwrap();

    _ = print_time_since(last, "verify done"); 

    Ok(())
}
