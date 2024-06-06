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
use std::fs::File;
use std::io::{BufRead, BufReader};
use ark_ff::BigInteger;
use sha256::try_digest;
use sha256::digest;
use std::path::Path;

use ark_std::rand::{RngCore, SeedableRng};
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::{CryptographicSponge, FieldBasedCryptographicSponge};

use ark_bls12_381::{G1Affine as GAffine};
use ark_ff::PrimeField;

use ark_groth16::Groth16;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_groth16::ProvingKey;
use ark_groth16::VerifyingKey;
use ark_groth16::Proof;

use num_bigint::BigUint;


use proc_status::ProcStatus;


static D : usize = 14;
static EXPONENT : u32 = 3;
static PIXEL_RANGE : i32 = 2_i32.pow(EXPONENT);
static HASH_LENGTH : usize = 128;

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


// Calculates lattice hash (Section 2.4.2)
fn calculate_full_hash(start: u128) -> Vec<Fr>{
    let rng = &mut test_rng();

    let mut hash = Vec::new();

    for _ in 0..HASH_LENGTH {
        hash.push(Fr::from(0));
    }

    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();
        let v_point = Fr::from(i as i32); //Fr::rand(rng);

        for j in 0..hash.len() {
            hash[j] += Fr::rand(rng) * v_point;
        }
    }
    return hash;
}

// Performs all prover work (i.e., polynomial calculations, commitments, and openings)
fn eval_polynomials(domain: GeneralEvaluationDomain::<Fr>, start: u128, instance_hash: &str, time_ck: &CommitterKey::<Bls12_381>)  
-> (Vec<Commitment<Bls12_381>>, Vec<Commitment<Bls12_381>>, Vec<Commitment<Bls12_381>>, Vec<Vec<Fr>>, Vec<Vec<Fr>>, Vec<Vec<Fr>>, Vec<Fr>, EvaluationProof<Bls12_381>, EvaluationProof<Bls12_381>, EvaluationProof<Bls12_381>)  {
    let mut rng = &mut test_rng();

    // polynomials will hold the polynomials we commit to
    let mut polynomials0 = Vec::new();

    // w_vals = [0, 1,...,PIXEL_RANGE - 1]
    let mut w_vals = Vec::new();
    for i in 0..PIXEL_RANGE {
        let i_in_fr = Fr::from(i);
        w_vals.push(i_in_fr);
    }

    // w[X] = poly(w_vals)
    let w = interpolate(w_vals, domain);
    println!("w done");
    polynomials0.push(w.coeffs.clone());

    // v_vals = [pixel_0,...,pixel_{D-1}]
    let mut v_vals = Vec::new();
    // z_vals = [sort(v || w)]
    let mut z_vals : Vec<Fr> = Vec::new();

    // reading in photo pixels...
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = Fr::from(i as i32); 
        v_vals.push(v_point);
        z_vals.push(v_point);

    }

    // v[X] = poly(v_vals)
    let v = interpolate(v_vals, domain);
    println!("v done");

    polynomials0.push(v.coeffs.clone());

    for i in 0..PIXEL_RANGE {
        let i_in_fr = Fr::from(i);
        z_vals.push(i_in_fr);
    }
    // pad z_vals so that [z[omega*x] - z[x][1 - (z[omega*x] - z[x])] = 0 still holds true
    let z_vals_length = z_vals.len();
    for _ in 0..domain.size() - z_vals_length {
        z_vals.push(Fr::from(PIXEL_RANGE - 1));
    }
    z_vals.sort();

    // z[X] = poly(z_vals)
    let z = interpolate(z_vals.clone(), domain);
    println!("z prods done");
    polynomials0.push(z.coeffs.clone());

    let time_batched_commitments0 = time_ck.batch_commit(&polynomials0);

    // permutation challenge
    let gamma = get_sha256_of_commitments(time_batched_commitments0.clone(), instance_hash, 2)[0];

    // Permutation argument
    // We want to prove:
    //           product_{i=0}^{D-1}(v_i + gamma) * product_{i=0}^{PIXEL_RANGE-1}(w_i + gamma) = product_{i=0}^{D + PIXEL_RANGE - 1}(z_i + gamma) 
    // where v holds the image pixels, w is the range that the pixel values must lie in [0, PIXEL_RANGE-1],
    // and z is the sorted concatentation of v and w

    let mut polynomials = Vec::new();

    // w_prod_vals = [1, (gamma), [(gamma)(1 + gamma)],...,[(gamma)...(PIXEL_RANGE - 1 + gamma)]]
    let mut w_prod_vals = Vec::new();
    let mut product = Fr::from(1u64);
    w_prod_vals.push(product);

    for i in 0..PIXEL_RANGE {
        let i_in_fr = Fr::from(i);
        product *= i_in_fr + gamma;
        w_prod_vals.push(product);
    }

    let w_prod_vals_len = w_prod_vals.len();
    for _ in 0..domain.size() - w_prod_vals_len {
        product *= gamma;
        w_prod_vals.push(product);
    }

    // w_prod_omega_vals = [(gamma), [(gamma)(1 + gamma)],...,[(gamma)...(PIXEL_RANGE + gamma)], 1]
    let mut w_prod_omega_vals = Vec::new();
    for i in 1..w_prod_vals.len() {
        w_prod_omega_vals.push(w_prod_vals[i]);
    }
    w_prod_omega_vals.push(w_prod_vals[0]);

    // for all i \in [1, PIXEL_RANGE + 1], w_prod[omega^i] = \prod_{j=0}^{i-1}(w_j + gamma)
    let w_prod = interpolate(w_prod_vals, domain);

    // w_prod_omega[X] = w_prod[omega*X]
    let w_prod_omega = interpolate(w_prod_omega_vals, domain);
    println!("w prods done");

    // n_1[X] = omega^{|domain| - 1} - X
    // We use n_1[X] to ensure that the permutation check equation holds for omega^{|domain} -1}
    let mut n_1_coeffs = Vec::new();
    n_1_coeffs.push(domain.group_gen().pow(&[(domain.size() - 1) as u64]));
    n_1_coeffs.push(Fr::from(-1));
    let n_1 = DensePolynomial::<Fr>::from_coefficients_vec(n_1_coeffs);

    let mut gamma_coeffs = Vec::new();
    gamma_coeffs.push(gamma);
    let gamma_poly = DensePolynomial::<Fr>::from_coefficients_vec(gamma_coeffs);

    // q_w[X] = (w_prod[omega * X] - (w_prod[X] * (gamma + w[X]))) * n_1[X] / Z_H[X]
    let (q_w, r_w) = (&(&w_prod_omega - &(&w_prod * &(&gamma_poly + &w))) * &n_1).divide_by_vanishing_poly(domain).unwrap();
    assert!(r_w.is_zero());

    println!("q_w done");

    // Will commit to w[X], w_prod[X], q_w[X]
    polynomials.push(w_prod.coeffs.clone());
    polynomials.push(q_w.coeffs.clone());

    // v_prod_vals = [1, (pixel_0 + gamma), [(pixel_0 + gamma)(pixel_1 + gamma)],...,[(pixel_0 + gamma)...(pixel_{D-1} + gamma)]]
    let mut v_prod_vals = Vec::new();
    let mut product = Fr::from(1u64);
    v_prod_vals.push(product);

    // reading in photo pixels...
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = Fr::from(i as i32); 

        product *= v_point + gamma;
        v_prod_vals.push(product);
    }

    for _ in 0..domain.size() - D - 1 {
        product *= gamma;
        v_prod_vals.push(product);
    }

    // v_prod_omega_vals = [(pixel_0 + gamma), [(pixel_0 + gamma)(pixel_1 + gamma)],...,[(pixel_0 + gamma)...(pixel_{D-1} + gamma)], 1]
    let mut v_prod_omega_vals = Vec::new();
    for i in 1..v_prod_vals.len() {
        v_prod_omega_vals.push(v_prod_vals[i]);
    }
    v_prod_omega_vals.push(v_prod_vals[0]);

    // for all i \in [1, D + 1], v_prod[omega^i] = \prod_{j=0}^{i-1}(v_j + gamma)
    let v_prod = interpolate(v_prod_vals, domain);

    // v_prod_omega[X] = v_prod[omega*X]
    let v_prod_omega = interpolate(v_prod_omega_vals, domain);
    println!("v prods done");

    // q_v[X] = (v_prod[omega * X] - (v_prod[X] * (gamma + v[X]))) * n_1[X] / Z_H[X]
    let (q_v, r_v) = (&(&v_prod_omega - &(&v_prod * &(&gamma_poly + &v))) * &n_1).divide_by_vanishing_poly(domain).unwrap();
    assert!(r_v.is_zero());
    println!("r_v prods done");

    // Will commit to v[X], v_prod[X], q_v[X]
    polynomials.push(v_prod.coeffs.clone());
    polynomials.push(q_v.coeffs.clone());

    // z_prod_vals = [1, z_vals_0 + gamma, [(z_0 + gamma)(z_vals_1 + gamma)],...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)]]
    let mut z_prod_vals = Vec::new();
    let mut product = Fr::from(1u64);
    z_prod_vals.push(product);
    for i in 0..z_vals.len() - 1 {
        product *= z_vals[i] + gamma;
        z_prod_vals.push(product);
    }

    // Range argument
    // We want to prove for the z constructed above that:
    //      (z[X] - z[omega*X])(1 - (z[X] - z[omega*X]) = 0 mod Z_H[X]

    // z_omega_vals = [z_vals_0 + gamma,...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)], 1]
    let mut z_omega_vals = Vec::new();
    for i in 1..z_vals.len() {
        z_omega_vals.push(z_vals[i]);
    }
    z_omega_vals.push(z_vals[0]);

    // z_prod_omega_vals = [z_vals_0 + gamma, [(z_vals_0 + gamma)(z_vals_1 + gamma)],...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)], 1]
    let mut z_prod_omega_vals = Vec::new();
    for i in 1..z_prod_vals.len() {
        z_prod_omega_vals.push(z_prod_vals[i]);
    }
    z_prod_omega_vals.push(z_prod_vals[0]);

    // for all i \in [1, PIXEL_RANGE + D], z_prod[omega^i] = \prod_{j=0}^{i-1}(z_j + gamma)
    let z_prod = interpolate(z_prod_vals, domain);

    // z_prod_omega[X] = z_prod[omega*X]
    let z_prod_omega = interpolate(z_prod_omega_vals, domain);
    println!("z_omega prods done");

    // q_v[X] = (v_prod[omega * X] - (v_prod[X] * (gamma + v[X]))) * n_1[X] / Z_H[X]
    let (q_z, r_z) = (&(&z_prod_omega - &(&z_prod * &(&gamma_poly + &z))) * &n_1).divide_by_vanishing_poly(domain).unwrap();
    assert!(r_z.is_zero());
    println!("q_z prods done");

    // z_omega[X] = z[omega*X]
    let z_omega = interpolate(z_omega_vals, domain);

    let mut one_coeffs = Vec::new();
    one_coeffs.push(Fr::from(1));
    
    let one = DensePolynomial::<Fr>::from_coefficients_vec(one_coeffs);
 
    // q_range[X] = (z[X] - z[omega*X])(1 - (z[X] - z[omega*X]) * n_1[X] / Z_H[X]
    let (q_range, r_range) = (&(&(&z_omega - &z) * &(&one - &(&z_omega - &z))) * &n_1).divide_by_vanishing_poly(domain).unwrap();

    assert!(r_range.is_zero());
    println!("r_range prods done");

    // Will commit to z[X], z_prod[X], q_z[X], q_range[X]
    polynomials.push(z_prod.coeffs.clone());
    polynomials.push(q_z.coeffs.clone());
    polynomials.push(q_range.coeffs.clone());

    // We commit in batches for memory reasons
    let time_batched_commitments1 = time_ck.batch_commit(&polynomials);
    println!("first commitment done");

    // Now we prove knowledge of actual hash value (Section 5.5) 
    // Want to generate a[X] and prove that Equation 11 in Section 5.5 holds for
    // this a[X] and the v[X] generated above

    // Use commitments to generate random coefficients [r_0,...,r_{HASH_LENGTH-1}]
    // for random linear combination of sum checks
    let hash_coeffs = get_sha256_of_commitments(time_batched_commitments1.clone(), "", HASH_LENGTH);

    let mut rng = &mut test_rng();

    // Let A be the public hashing matrix (we will generate it with a PRG)
    // a_vals = [\sum_{i=0}{HASH_LENGTH-1}r_i * A_{i, 0},...,\sum_{i=0}{HASH_LENGTH-1}r_i * A_{i, D - 1}]
    let mut a_vals = Vec::new();

    // h_sum_vals = [0, v_vals_0 * a_vals_0 ,..., \sum_{i=0}^{D - 1} v_vals_0 * a_vals_0]
    let mut h_sum_vals = Vec::new();

    // h_sum_omega_vals = [\sum_{i=0}^{1} v_vals_0 * a_vals_0,...,\sum_{i=0}^{D - 1} v_vals_0 * a_vals_0, v_vals_0 * a_vals_0]
    let mut h_sum_omega_vals = Vec::new();
    h_sum_vals.push(Fr::from(0u64));
    let mut sum = Fr::from(0u64);

    // Re-read in pixels
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = Fr::from(i as i32); 

        let mut a_point = Fr::from(0); 
        for j in 0..hash_coeffs.len() {
            a_point += Fr::rand(rng) * hash_coeffs[j];
        }
        a_vals.push(a_point);

        sum += v_point * a_point;
        h_sum_vals.push(sum);
        h_sum_omega_vals.push(sum);
    }

    for _ in 0..domain.size() - D - 1 {
        h_sum_vals.push(sum);
        h_sum_omega_vals.push(sum);
    }
    h_sum_omega_vals.push(Fr::from(0u64));


    // for all i \in [0, D - 1], a[omega^i] = \sum_{j=0}{HASH_LENGTH-1}r_j * A_{j, i}
    let a = interpolate(a_vals, domain); 

    // for all i \in [0, D], h_sum[omega^i] = \sum_{j=0}^{i} v_vals_j * a_vals_j
    let h_sum = interpolate(h_sum_vals, domain);

    // h_sum_omega[X] = h_sum[omega*X]
    let h_sum_omega = interpolate(h_sum_omega_vals, domain);
    println!("h_sum_omega prods done");

    // q_h_sum[X] = (h_sum[omega*X] - h_sum[X] - (v[X] * a[X]))* n_1[X] / Z_H[X]
    let (q_h_sum, r_h_sum) = (&(&(&h_sum_omega - &h_sum) - &(&v * &a))* &n_1).divide_by_vanishing_poly(domain).unwrap();
    assert!(r_h_sum.is_zero());
    println!("q_h_sum prods done");

    // Second set of polynomials we commit to
    let mut polynomials2 = Vec::new();
    let mut evals2 = Vec::new();

    // Will commit to a[X], h_sum[X], q_h_sum[X]
    polynomials2.push(a.coeffs.clone());
    polynomials2.push(h_sum.coeffs.clone());
    polynomials2.push(q_h_sum.coeffs.clone());

    // Commit
    let time_batched_commitments2 = time_ck.batch_commit(&polynomials2);
    println!("second commitment done");

    // PRODUCE OPENING PROOFS

    // alpha is random challenge that we get by hashing commitments (i.e., we use Fiat-Shamir)
    // eta1 and eta2 are the challenges we use to batch evaluation proofs
    let hashes = get_sha256_of_commitments(time_batched_commitments2.clone(), "", 4);
    let alpha = hashes[0];
    let eta0 = hashes[1];
    let eta1 = hashes[2];
    let eta2 = hashes[3];

    // We batch open all committed polynomials at alpha, omega*alpha D, PIXEL_RANGE, D + PIXEL_RANGE
    let mut eval_points = Vec::new();
    eval_points.push(alpha);
    eval_points.push(domain.group_gen() * alpha);
    eval_points.push(domain.group_gen().pow(&[(D) as u64]));
    eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
    eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64]));

    // Evaluate zeroth set of batched polynomials
    // evals0 will hold the evaluations of the polynomials
    let mut evals0 = Vec::new();

    let mut w_evals = Vec::new();
    for x in eval_points.iter() {
        w_evals.push(w.evaluate(x));
    }
    evals0.push(w_evals);
     let mut v_evals = Vec::new();
    for x in eval_points.iter() {
        v_evals.push(v.evaluate(x));
    }
    evals0.push(v_evals);
    let mut z_evals = Vec::new();
    for x in eval_points.iter() {
        z_evals.push(z.evaluate(x));
    }
    evals0.push(z_evals);

    let proof0 = time_ck.batch_open_multi_points(
        &polynomials0.iter().collect::<Vec<_>>(),
        &eval_points,
        &eta0,
    );
    println!("zeroth proof done");

    // Evaluate first set of batched polynomials
    // evals will hold the evaluations of the polynomials
    let mut evals1 = Vec::new();

    let mut w_prod_evals = Vec::new();
    for x in eval_points.iter() {
        w_prod_evals.push(w_prod.evaluate(x));
    }
    evals1.push(w_prod_evals);

    let mut q_w_evals = Vec::new();
    for x in eval_points.iter() {
        q_w_evals.push(q_w.evaluate(x));
    }
    evals1.push(q_w_evals);

    let mut v_prod_evals = Vec::new();
    for x in eval_points.iter() {
        v_prod_evals.push(v_prod.evaluate(x));
    }
    
    evals1.push(v_prod_evals);

    let mut q_v_evals = Vec::new();
    for x in eval_points.iter() {
        q_v_evals.push(q_v.evaluate(x));
    }
    evals1.push(q_v_evals);

    let mut z_prod_evals = Vec::new();
    for x in eval_points.iter() {
        z_prod_evals.push(z_prod.evaluate(x));
    }
    evals1.push(z_prod_evals);

    let mut q_z_evals = Vec::new();
    for x in eval_points.iter() {
        q_z_evals.push(q_z.evaluate(x));
    }   
    evals1.push(q_z_evals);

    let mut q_range_evals = Vec::new();
    for x in eval_points.iter() {
        q_range_evals.push(q_range.evaluate(x));
    }   
    evals1.push(q_range_evals);

    // Produce opening proofs for first set of batched commitments
    let proof1 = time_ck.batch_open_multi_points(
        &polynomials.iter().collect::<Vec<_>>(),
        &eval_points,
        &eta1,
    );
    println!("first proof done");

    // Evaluate second set of batched polynomials
    let mut a_evals = Vec::new();
    for x in eval_points.iter() {
        a_evals.push(a.evaluate(x));
    }
    evals2.push(a_evals);

    let mut h_sum_evals = Vec::new();
    for x in eval_points.iter() {
        h_sum_evals.push(h_sum.evaluate(x));
    }
    evals2.push(h_sum_evals);

    let mut q_h_sum_evals = Vec::new();
    for x in eval_points.iter() {
        q_h_sum_evals.push(q_h_sum.evaluate(x));
    }
    evals2.push(q_h_sum_evals);

    // Produce opening proofs for second set of batched commitments
    // let eta2: Fr = u128::rand(&mut rng).into();
    let proof2 = time_ck.batch_open_multi_points(
        &polynomials2.iter().collect::<Vec<_>>(),
        &eval_points,
        &eta2,
    );
    println!("second proof done");
    

    return (time_batched_commitments0, time_batched_commitments1, time_batched_commitments2, evals0, evals1, evals2, hash_coeffs, proof0, proof1, proof2);
}


fn get_filename(prefix: &str) -> String {
    let mut filename = prefix.to_owned();
    filename.push_str("image_");
    filename.push_str(&D.to_string());
    filename.push_str("_");
    filename.push_str(&EXPONENT.to_string());
    filename.push_str(".txt");
    return filename
}

fn read_photo(prefix: &str) -> BufReader<File> {
    let file = File::open(get_filename(prefix)).expect("Unable to open file");
    return BufReader::new(file);
}

// gets sha256 of commitments for random challenges
fn get_sha256_of_commitments(commitments: Vec<Commitment<Bls12_381>>, instance_hash: &str, num_elements: usize) -> Vec<Fr> {
    let mut byte_vec = Vec::new();
    for commitment in commitments {
        let affine_rep = GAffine::from(commitment.0);
        let mut bytes_x1 = affine_rep.x.into_bigint().to_bytes_le();
        let mut bytes_y1 = affine_rep.y.into_bigint().to_bytes_le();

        byte_vec.append(&mut bytes_x1);
        byte_vec.append(&mut bytes_y1);
        
    }

    let s = format!("{:?}{:?}", &byte_vec, instance_hash);
    let mut val = digest(s);

    let mut ret = Vec::new();

    for _ in 0..num_elements/2 {
        let sha2561 = u128::from_str_radix(&val[0..32], 16).unwrap();
        ret.push(Fr::from(sha2561));
        let sha2562 = u128::from_str_radix(&val[32..64], 16).unwrap();
        ret.push(Fr::from(sha2562));
        val = digest(val);
    }
    
    return ret;
}

// Circuit public key/verification key setup
fn poseidon_circuit_setup(input: Vec<Fr>, coeffs: Vec<Fr>, hash: Fr, linear_combo_hash: Fr) -> (ProvingKey<Bls12_381>, VerifyingKey<Bls12_381>) {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let (pk, vk) = {
        let c = AbsorbCircuit::<Fr>::new(input, coeffs, hash, linear_combo_hash);
        Groth16::<Bls12_381>::setup(c, &mut rng).unwrap()
    };

    return (pk, vk);
}

// Prove circuit to verify short_hash = PoseidonHash(full_hash) and linear_combo_hash = hash_coeffs \dot full_hash
fn prove_poseidon_circuit(input: Vec<Fr>, coeffs: Vec<Fr>, hash: Fr, linear_combo_hash: Fr, pk: ProvingKey<Bls12_381>) -> Proof<Bls12_381> {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let c = AbsorbCircuit::<Fr>::new(input, coeffs, hash, linear_combo_hash);
    return Groth16::<Bls12_381>::prove(&pk, c, &mut rng).unwrap();
}

// Verify Poseidon hashing circuit
fn verify_poseidon_circuit(proof: Proof<Bls12_381>, vk: VerifyingKey<Bls12_381>, coeffs: Vec<Fr>, hash: Fr, linear_combo_hash: Fr) {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let mut inputs = Vec::new();
    for i in 0..HASH_LENGTH {
        inputs.push(coeffs[i]);
    }
    inputs.push(hash);
    inputs.push(linear_combo_hash);

    let res = Groth16::<Bls12_381>::verify(&vk, &inputs, &proof).unwrap();
    assert!(res);
}


// Calculates Poseidon hash
fn get_poseidon_hash(input: &Vec<Fr>, num_elements: usize) -> Vec<Fr> {
    let sponge_params = poseidon_parameters_for_test();
    let mut native_sponge = PoseidonSponge::<Fr>::new(&sponge_params);
    native_sponge.absorb(&input);
    return native_sponge.squeeze_native_field_elements(num_elements); 
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
    last = print_time_since(start, last, "domain generated calculated"); 

    // Get PoseidonHash(LatticeHash(originalPhoto)) 
    // In practice, this value is directly given to the verifier. We only rederive it here 
    // for ease of programming
    let full_hash = calculate_full_hash(start);
    last = print_time_since(start, last, "calculate_full_hash done"); 
    let short_hash = get_poseidon_hash(&full_hash, 1)[0];
    last = print_time_since(start, last, "lattice hash calculated"); 


    // Hash edited photo (instance)
    let filename = get_filename("edited_");
    let input = Path::new(&filename);
    let binding = try_digest(input).unwrap();
    let instance_hash = binding.as_str();

    // Generate proving and verification keys for Poseidon circuit
    let mut vec_placeholder = Vec::new();
    for _ in 0..HASH_LENGTH {
        vec_placeholder.push(Fr::from(0));
    }
    let (pk, vk) = poseidon_circuit_setup(vec_placeholder.clone(), vec_placeholder.clone(), Fr::from(0), Fr::from(0));

    // Generate committer and verification key
    let rng = &mut test_rng();
    let time_ck = CommitterKey::<Bls12_381>::new(domain.size() - 1, 5, rng);
    let time_vk = VerifierKey::from(&time_ck);

    last = print_time_since(start, last, "SETUP TOOK"); 

// ===================================================================================================================================

    // PROVER WORK
    // Create commitments, opening proofs, and claimed evaluations
    let (coms0, coms1, coms2, evals0, evals1, evals2, prover_hash_coeffs, proof0, proof1, proof2) = eval_polynomials(domain, start, instance_hash.clone(), &time_ck);
    // Create Groth16 proof to verify short_hash=PoseidonHash(full_hash) and linear_combo_hash = hash_coeffs \dot full_hash
    let proof = prove_poseidon_circuit(full_hash, prover_hash_coeffs.clone(), short_hash, evals2[1][2], pk);

    last = print_time_since(start, last, "PROVER TOOK");     

// ===================================================================================================================================

    // VERIFIER WORK

    // Rederive random coefficients and challenges
    let gamma = get_sha256_of_commitments(coms0.clone(), instance_hash, 2)[0];
    let hash_coeffs = get_sha256_of_commitments(coms1.clone(), "", HASH_LENGTH);
    let hashes = get_sha256_of_commitments(coms2.clone(), "", 4);
    let alpha = hashes[0];
    let eta0 = hashes[1];
    let eta1 = hashes[2];
    let eta2 = hashes[3];

    // Re-generate eval_points
    let mut eval_points = Vec::new();
    eval_points.push(alpha);
    eval_points.push(domain.group_gen() * alpha);
    eval_points.push(domain.group_gen().pow(&[(D) as u64]));
    eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
    eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64])); 

    // Verify all commitment evaluation proofs
    let verification_result = time_vk.verify_multi_points(
        &coms0,
        &eval_points,
        &evals0,
        &proof0,
        &eta0,
    );
    assert!(verification_result.is_ok()); 
    println!("zeroth verification done");

    let verification_result = time_vk.verify_multi_points(
        &coms1,
        &eval_points,
        &evals1,
        &proof1,
        &eta1,
    );
    assert!(verification_result.is_ok()); 
    println!("first verification done");
    let verification_result = time_vk.verify_multi_points(
        &coms2,
        &eval_points,
        &evals2,
        &proof2,
        &eta2,
    );
    assert!(verification_result.is_ok()); 
    println!("second verification done");

    let mut rng = &mut test_rng();

    // Re-generate a such that for all i \in [0, D - 1], a[omega^i] = \sum_{j=0}{HASH_LENGTH-1}r_j * A_{j, i}
    let mut a_vals = Vec::new();
    for i in 0..D {
        let mut a_point = Fr::from(0); 
        for j in 0..hash_coeffs.len() {
            let rand = Fr::rand(rng);
            a_point += rand * hash_coeffs[j];
        }
        a_vals.push(a_point);
    }
    // for all i \in [0, D - 1], a[omega^i] = \sum_{j=0}{HASH_LENGTH-1}r_j * A_{j, i}
    let a = interpolate(a_vals, domain); 

    // n_1[X] = omega^{|domain| - 1} - X
    let mut n_1_coeffs = Vec::new();
    n_1_coeffs.push(domain.group_gen().pow(&[(domain.size() - 1) as u64]));
    n_1_coeffs.push(Fr::from(-1));
    let n_1 = DensePolynomial::<Fr>::from_coefficients_vec(n_1_coeffs);
    let n_1_of_alpha = n_1.evaluate(&alpha);

    // evals0
    // w, v, z

    // evals1
    // w_prod, q_w, v_prod, q_v, z_prod, q_z, q_range

    // Permutation Checks
    // Check (w_prod[omega*alpha] - w_prod[alpha](gamma + w[alpha])) * n_1[alpha] = q_w[alpha] * Z_H[alpha]
    assert!((evals1[0][1] - evals1[0][0] * (gamma + evals0[0][0])) * n_1_of_alpha == evals1[1][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check (v_prod[omega*alpha] - v_prod[alpha](gamma + v[alpha])) * n_1[alpha] = q_v[alpha] * Z_H[alpha]
    assert!((evals1[2][1] - evals1[2][0] * (gamma + evals0[1][0])) * n_1_of_alpha == evals1[3][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check (z_prod[omega*alpha] - z_prod[alpha](gamma + z[alpha])) * n_1[alpha] = q_z[alpha] * Z_H[alpha]
    assert!((evals1[4][1] - evals1[4][0] * (gamma + evals0[2][0])) * n_1_of_alpha == evals1[5][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check v_prod[omega^D] * w_prod[omega^PIXEL_RANGE] = z_prod[omega^{D + PIXEL_RANGE}]
    assert!(evals1[2][2] * evals1[0][3] == evals1[4][4]);

    // Range Checks
    // Check n_1[alpha] * (z[omega*alpha] - z[alpha]) (1 - z[omega*alpha] - z[alpha]) = q_range[alpha] * Z_H[alpha]
    let dif = evals0[2][1] - evals0[2][0]; 
    assert!(n_1_of_alpha * dif * (Fr::from(1u64) - dif) == evals1[6][0] * domain.evaluate_vanishing_polynomial(alpha));

    // Hash Value Checks
    // Check (h_sum[omega*alpha] - h_sum[alpha] - v[alpha] * a[alpha]) * n_1[alpha] =  q_h_sum[alpha] * Z_H[alpha]
    assert!((evals2[1][1] - evals2[1][0] - evals0[1][0] * a.evaluate(&alpha)) * n_1_of_alpha  == evals2[2][0] * domain.evaluate_vanishing_polynomial(alpha));
 
    // Verify Groth16 proof
    let linear_combo_hash = evals2[1][2];
    verify_poseidon_circuit(proof, vk, hash_coeffs, short_hash, linear_combo_hash);

    println!("{}", linear_combo_hash);
    println!("{}", short_hash);

    _ = print_time_since(start, last, "VERIFIER TOOK"); 

    let mem = proc_status::mem_usage().unwrap();
    println!("Mem usage in bytes: current={}, peak={}", mem.current, mem.peak);


}