use ark_bls12_381::{Bls12_381, Fr};

use ark_gemini::absorbcircuit::{AbsorbCircuit, poseidon_parameters_for_test};

use ark_poly::univariate::DensePolynomial;
use ark_poly::{Polynomial};
use ark_std::test_rng;
use ark_std::UniformRand;
use ark_poly::domain::EvaluationDomain;
use ark_poly::domain::general::GeneralEvaluationDomain;
use ark_poly::evaluations::univariate::Evaluations;
use ark_gemini::kzg::CommitterKey;
use ark_gemini::kzg::VerifierKey;
use std::time::{SystemTime, UNIX_EPOCH};
use ark_poly::DenseUVPolynomial;
use ark_std::Zero;
use ark_ff::fields::Field;
use ark_gemini::kzg::Commitment;
use ark_gemini::kzg::EvaluationProof;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, BufWriter, Write};
use ark_ff::BigInteger;
use sha256::try_digest;
use std::path::Path;
use ark_gemini::misc::evaluate_le;
use std::fs;
use std::str::FromStr;

use ark_std::rand::{RngCore, SeedableRng};
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::{CryptographicSponge, FieldBasedCryptographicSponge};

use ark_bls12_381::{G1Affine as GAffine, G1Projective as G};
use ark_ff::PrimeField;

use ark_groth16::Groth16;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_groth16::ProvingKey;
use ark_groth16::VerifyingKey;
use ark_groth16::Proof;

use proc_status::ProcStatus;

use num_bigint::BigUint;



static D : usize = 14;
static EXPONENT : u32 = 3;
static PIXEL_RANGE : i32 = 2_i32.pow(EXPONENT);
static HASH_LENGTH : usize = 128;
static BATCH_SIZE : usize = 16;

fn print_time_since(start: u128, last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!("{:?}; time since start {:?}; time since last check: {:?}", tag, (now - start) as f32 / 60000.0, (now - last) as f32 / 60000.0); 
    return now;
}

// ConvertVecToPoly (Section 5.1)
fn interpolate(vals : Vec<Fr>, domain: GeneralEvaluationDomain::<Fr>) -> DensePolynomial<Fr> {
    let evaluations = Evaluations::<Fr, GeneralEvaluationDomain<Fr>>::from_vec_and_domain(vals, domain);
    return evaluations.interpolate();
}

fn read_commitments() -> BufReader<File> {
    let mut filename = "coms_".to_owned();
    filename.push_str(&D.to_string());
    filename.push_str("_");
    filename.push_str(&EXPONENT.to_string());
    filename.push_str(".txt");
    let file = File::open(filename).expect("Unable to open file");
    return BufReader::new(file);
}


fn main() {
// ===================================================================================================================================
    
    // SETUP 

    // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    // Generates domain large enough for proving
    let domain = GeneralEvaluationDomain::<Fr>::new(D + PIXEL_RANGE as usize).unwrap();


    // Generate committer and verification key
    let mut rng = &mut test_rng();
    let time_ck = CommitterKey::<Bls12_381>::new(domain.size() - 1, 5, rng);
    let time_vk = VerifierKey::from(&time_ck);

    last = print_time_since(start, last, "finished domain"); 

// ===================================================================================================================================
    

    // Pre-commits to all row polynomials

    // let mut all_evals = Vec::new();
    let mut all_commitments = Vec::new();
        
    for batch in 0..HASH_LENGTH / BATCH_SIZE {
        let mut rng = &mut test_rng();
        let mut a_vals_vec = Vec::new();

        for i in 0..BATCH_SIZE {
            a_vals_vec.push(Vec::new());
        }

        for i in 0..D {
            for j in 0..HASH_LENGTH {
                let rand = Fr::rand(rng);
                if j / BATCH_SIZE == batch {
                    a_vals_vec[j % BATCH_SIZE].push(rand);
                }
                
            }
        }

        let mut polynomials = Vec::new();
        let mut a_polys = Vec::new();
        for i in 0..BATCH_SIZE {
            let a = interpolate(a_vals_vec[i].clone(), domain);
            polynomials.push(a.clone().coeffs);
            a_polys.push(a);
        } 


        last = print_time_since(start, last, "finished interpolating"); 

        let time_batched_commitments = time_ck.batch_commit(&polynomials);
        all_commitments.push(time_batched_commitments.clone());

        last = print_time_since(start, last, "finished committing"); 
 
        /*let mut eval_points = Vec::new();
        let alpha = Fr::from(num_bigint::BigUint::from_str("49459846424658789300028684371166904060672975076450753235880665927999160481389").unwrap());
        eval_points.push(alpha);
        eval_points.push(domain.group_gen() * alpha);
        eval_points.push(domain.group_gen().pow(&[(D) as u64]));
        eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
        eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64])); 

        let mut evals = Vec::new();
        for poly in a_polys {
            let mut poly_evals = Vec::new();
            for x in eval_points.iter() {
                poly_evals.push(poly.evaluate(x));
            }
            all_evals.push(poly_evals.clone());
            evals.push(poly_evals);
        }*/

        let mut filename = "A_".to_owned();
        filename.push_str(&D.to_string());
        filename.push_str("_");
        filename.push_str(&EXPONENT.to_string());
        filename.push_str("_");
        filename.push_str(&batch.to_string());
        filename.push_str(".txt");

        let f = File::create(filename).expect("Unable to create file");
        let mut f = BufWriter::new(f);
        for commitment in &time_batched_commitments {
            let affine_rep = GAffine::from(commitment.0);
            let x: num_bigint::BigUint = affine_rep.x.into();
            let y: num_bigint::BigUint = affine_rep.y.into();
            writeln!(f, "{}", x.to_string());
            writeln!(f, "{}", y.to_string());
        }
        drop(f);

    }

    // Write all commitments
    /*for i in 0..HASH_LENGTH / BATCH_SIZE {
        let mut filename = "A_".to_owned();
        filename.push_str(&D.to_string());
        filename.push_str("_");
        filename.push_str(&EXPONENT.to_string());
        filename.push_str("_");
        filename.push_str(&i.to_string());
        filename.push_str(".txt");

        let f = File::create(filename).expect("Unable to create file");
        let mut f = BufWriter::new(f);
        for commitment in &all_commitments[i] {
            let affine_rep = GAffine::from(commitment.0);
            let x: num_bigint::BigUint = affine_rep.x.into();
            let y: num_bigint::BigUint = affine_rep.y.into();
            writeln!(f, "{}", x.to_string());
            writeln!(f, "{}", y.to_string());
        }
        drop(f);
    }*/


    /*let mut new_commitments = Vec::new();

    for i in 0..HASH_LENGTH / BATCH_SIZE {

        let mut commitments = Vec::new();

        let mut filename = "A_".to_owned();
        filename.push_str(&D.to_string());
        filename.push_str("_");
        filename.push_str(&EXPONENT.to_string());
        filename.push_str("_");
        filename.push_str(&i.to_string());
        filename.push_str(".txt");

        let mut newx = num_bigint::BigUint::from_str("0").unwrap();
        let mut newy = num_bigint::BigUint::from_str("0").unwrap();

        let f = File::open(filename).expect("Unable to open file");
        let f = BufReader::new(f);

        let mut i = 0;
        for line in f.lines() {
            let line = line.expect("Unable to read line");
            if i % 2 == 0 {
                newx = num_bigint::BigUint::from_str(&line).unwrap();
            } else {
                newy = num_bigint::BigUint::from_str(&line).unwrap();
                let gaf = GAffine::new(newx.clone().into(), newy.clone().into());
                let g = G::from(gaf);
                let com : Commitment<Bls12_381> = Commitment(g);

                commitments.push(com);
            }
            i += 1;
        }
        new_commitments.push(commitments);
    }

    for i in 0..all_commitments.len() {
        for j in 0..all_commitments[i].len() {
            assert!(all_commitments[i][j] == new_commitments[i][j]);
        }
    }

    // you'll probably have to generate these one at a time
    let mut rng = &mut test_rng();
    let mut a_vals_vec = Vec::new();
    for i in 0..HASH_LENGTH {
        a_vals_vec.push(Vec::new());
    }
    for i in 0..D {
        for j in 0..HASH_LENGTH {
            let rand = Fr::rand(rng);
            a_vals_vec[j].push(rand);
        }
    }
    let mut polynomials = Vec::new();
    let mut a_polys = Vec::new();
    for i in 0..HASH_LENGTH {
        let a = interpolate(a_vals_vec[i].clone(), domain);
        polynomials.push(a.clone().coeffs);
        a_polys.push(a);
    } 

    last = print_time_since(start, last, "finished interpolating"); 
    
    let mut eval_points = Vec::new();
    eval_points.push(alpha);
    eval_points.push(domain.group_gen() * alpha);
    eval_points.push(domain.group_gen().pow(&[(D) as u64]));
    eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
    eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64])); 

    let mut evals = Vec::new();


    for poly in a_polys {
        let mut poly_evals = Vec::new();
        for x in eval_points.iter() {
            poly_evals.push(poly.evaluate(x));
        }
        evals.push(poly_evals);
    }

    assert!(all_evals == evals);

    // Test opening commitments
    for batch in 0..HASH_LENGTH / BATCH_SIZE {
        let mut rng = &mut test_rng();
        let mut a_vals_vec = Vec::new();

        for i in 0..BATCH_SIZE {
            a_vals_vec.push(Vec::new());
        }

        for i in 0..D {
            for j in 0..HASH_LENGTH {
                let rand = Fr::rand(rng);
                if j / BATCH_SIZE == batch {
                    a_vals_vec[j % BATCH_SIZE].push(rand);
                }
                
            }
        }

        let mut polynomials = Vec::new();
        let mut a_polys = Vec::new();
        for i in 0..BATCH_SIZE {
            let a = interpolate(a_vals_vec[i].clone(), domain);
            polynomials.push(a.clone().coeffs);
            a_polys.push(a);
        } 


        last = print_time_since(start, last, "finished interpolating"); 

 
        let mut eval_points = Vec::new();
        eval_points.push(alpha);
        eval_points.push(domain.group_gen() * alpha);
        eval_points.push(domain.group_gen().pow(&[(D) as u64]));
        eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
        eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64])); 

        let mut evals = Vec::new();
        for poly in a_polys {
            let mut poly_evals = Vec::new();
            for x in eval_points.iter() {
                poly_evals.push(poly.evaluate(x));
            }
            evals.push(poly_evals);
        }

        let eta1 = Fr::from(123);
        let proof = time_ck.batch_open_multi_points(
            &polynomials.iter().collect::<Vec<_>>(),
            &eval_points,
            &eta1,
        );
        last = print_time_since(start, last, "finished opening");

        let verification_result = time_vk.verify_multi_points(
            &new_commitments[batch],
            &eval_points,
            &evals,
            &proof,
            &eta1,
        );
        assert!(verification_result.is_ok()); 
    } */

    _ = print_time_since(start, last, "finished"); 

    let mem = proc_status::mem_usage().unwrap();
    println!("Mem usage in bytes: current={}, peak={}", mem.current, mem.peak);


}

