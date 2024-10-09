use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use std::time::{SystemTime, UNIX_EPOCH};

use rand::rngs::OsRng;
use rand::Rng;

static OLD_SIZE : usize = 10;
static NEW_SIZE : usize = 3;

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

    // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    let mut w_r_vals = Vec::new();
    let mut x_r_vals = Vec::new();

    for _ in 0..OLD_SIZE {
        w_r_vals.push(rng.gen_range(0..256) as u32);
    }

    for i in 0..NEW_SIZE {
        x_r_vals.push(w_r_vals[i]);
    }

    last = print_time_since(last, "values generated"); 
   
    let mut config = CircuitConfig::standard_recursion_config();
    config.zero_knowledge = true;
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut pw = PartialWitness::new();

    let mut w_r_targets = Vec::new();

    for _ in 0..NEW_SIZE {
        let r = builder.add_virtual_target();
        w_r_targets.push(r);
        builder.register_public_input(r);    
    }
        

    let data = builder.build::<C>();
    last = print_time_since(last, "setup done"); 

    for i in 0..NEW_SIZE {
        pw.set_target(w_r_targets[i], F::from_canonical_u32(w_r_vals[i]));
    }

    let proof = data.prove(pw)?;
    let compressed_proof = data.compress(proof)?;

    last = print_time_since(last, "proof done");

 //   println!("proof.public_inputs: {:?}", proof.public_inputs); 

    let decompressed_compressed_proof = data.decompress(compressed_proof)?;


    for i in 0..decompressed_compressed_proof.public_inputs.len() {
        assert!((decompressed_compressed_proof.public_inputs[i].0) as u32 == x_r_vals[i]);
    }

    let res = data.verify(decompressed_compressed_proof);
    let _ = res.unwrap();

    

    _ = print_time_since(last, "verify done"); 

    Ok(())
}
