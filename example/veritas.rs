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


static D : usize =14;
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
fn eval_polynomials(domain: GeneralEvaluationDomain::<Fr>, start: u128, gamma: Fr, time_ck: CommitterKey::<Bls12_381>)  
-> (Vec<Commitment<Bls12_381>>, Vec<Commitment<Bls12_381>>, Vec<Vec<Fr>>, Vec<Vec<Fr>>, Vec<Fr>, EvaluationProof<Bls12_381>, EvaluationProof<Bls12_381>)  {
    let mut rng = &mut test_rng();

    // polynomials will hold the polynomials we commit to
    let mut polynomials = Vec::new();

    // evals will hold the evaluations of the polynomials
    let mut evals = Vec::new();


    // Permutation argument (Section 5.3)
    // We want to prove:
    //           product_{i=0}^{D-1}(v_i + gamma) * product_{i=0}^{PIXEL_RANGE-1}(w_i + gamma) = product_{i=0}^{D + PIXEL_RANGE - 1}(z_i + gamma) 
    // where v holds the image pixels, w is the range that the pixel values must lie in [0, PIXEL_RANGE-1],
    // and z is the sorted concatentation of v and w

    // w_vals = [0, 1,...,PIXEL_RANGE - 1]
    let mut w_vals = Vec::new();

    // w_prod_vals = [1, (gamma), [(gamma)(1 + gamma)],...,[(gamma)...(PIXEL_RANGE - 1 + gamma)]]
    let mut w_prod_vals = Vec::new();
    let mut product = Fr::from(1u64);
    w_prod_vals.push(product);

    for i in 0..PIXEL_RANGE {
        let i_in_fr = Fr::from(i);
        w_vals.push(i_in_fr);

        product *= i_in_fr + gamma;
        w_prod_vals.push(product);
    }

    let w_prod_vals_len = w_prod_vals.len();
    for _ in 0..domain.size() - w_prod_vals_len {
        product *= gamma;
        w_prod_vals.push(product);
    }

    // w[X] = ConvertVecToPoly(w_vals)
    let w = interpolate(w_vals, domain);
    println!("w done");

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
    polynomials.push(w.coeffs.clone());
    polynomials.push(w_prod.coeffs.clone());
    polynomials.push(q_w.coeffs.clone());

    // v_vals = [pixel_0,...,pixel_{D-1}]
    let mut v_vals = Vec::new();
    // z_vals = [sort(v || w)]
    let mut z_vals : Vec<Fr> = Vec::new();

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
        v_vals.push(v_point);
        z_vals.push(v_point);

        product *= v_point + gamma;
        v_prod_vals.push(product);
    }

    for _ in 0..domain.size() - D - 1 {
        product *= gamma;
        v_prod_vals.push(product);
    }

    // v[X] = ConvertVecToPoly(v_vals)
    let v = interpolate(v_vals, domain);
    println!("v done");

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
    polynomials.push(v.coeffs.clone());
    polynomials.push(v_prod.coeffs.clone());
    polynomials.push(q_v.coeffs.clone());

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

    // z_prod_vals = [1, z_vals_0 + gamma, [(z_0 + gamma)(z_vals_1 + gamma)],...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)]]
    let mut z_prod_vals = Vec::new();
    let mut product = Fr::from(1u64);
    z_prod_vals.push(product);
    for i in 0..z_vals.len() - 1 {
        product *= z_vals[i] + gamma;
        z_prod_vals.push(product);
    }

    // Range argument (Section 5.4) 
    // We want to prove for the z constructed above that:
    //      (z[X] - z[omega*X])(1 - (z[X] - z[omega*X]) = 0 mod Z_H[X]

    // z_omega_vals = [z_vals_0 + gamma,...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)], 1]
    let mut z_omega_vals = Vec::new();
    for i in 1..z_vals.len() {
        z_omega_vals.push(z_vals[i]);
    }
    z_omega_vals.push(z_vals[0]);

    // z[X] = ConvertVecToPoly(z_vals)
    let z = interpolate(z_vals, domain);
    println!("z prods done");

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
    polynomials.push(z.coeffs.clone());
    polynomials.push(z_prod.coeffs.clone());
    polynomials.push(q_z.coeffs.clone());
    polynomials.push(q_range.coeffs.clone());

    // We commit in batches for memory reasons
    let time_batched_commitments = time_ck.batch_commit(&polynomials);
    println!("first commitment done");

    // Now we prove knowledge of actual hash value (Section 5.5) 
    // Want to generate a[X] and prove that Equation 11 in Section 5.5 holds for
    // this a[X] and the v[X] generated above

    // Use commitments to generate random coefficients [r_0,...,r_{HASH_LENGTH-1}]
    // for random linear combination of sum checks
    let hash_coeffs = get_poseidon_hash_of_commmitments(time_batched_commitments.clone(), HASH_LENGTH);

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
    let hashes = get_poseidon_hash_of_commmitments(time_batched_commitments2.clone(), 3);
    let alpha = hashes[0];
    let eta1 = hashes[1];
    let eta2 = hashes[2];

    // We batch open all committed polynomials at alpha, omega*alpha D, PIXEL_RANGE, D + PIXEL_RANGE
    let mut eval_points = Vec::new();
    eval_points.push(alpha);
    eval_points.push(domain.group_gen() * alpha);
    eval_points.push(domain.group_gen().pow(&[(D) as u64]));
    eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
    eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64]));

    // Evaluate first set of batched polynomials
    let mut w_evals = Vec::new();
    for x in eval_points.iter() {
        w_evals.push(w.evaluate(x));
    }
    evals.push(w_evals);
    
    let mut w_prod_evals = Vec::new();
    for x in eval_points.iter() {
        w_prod_evals.push(w_prod.evaluate(x));
    }
    evals.push(w_prod_evals);

    let mut q_w_evals = Vec::new();
    for x in eval_points.iter() {
        q_w_evals.push(q_w.evaluate(x));
    }
    evals.push(q_w_evals);

    let mut v_evals = Vec::new();
    for x in eval_points.iter() {
        v_evals.push(v.evaluate(x));
    }
    evals.push(v_evals);

    let mut v_prod_evals = Vec::new();
    for x in eval_points.iter() {
        v_prod_evals.push(v_prod.evaluate(x));
    }
    
    evals.push(v_prod_evals);

    let mut q_v_evals = Vec::new();
    for x in eval_points.iter() {
        q_v_evals.push(q_v.evaluate(x));
    }
    evals.push(q_v_evals);

    let mut z_evals = Vec::new();
    for x in eval_points.iter() {
        z_evals.push(z.evaluate(x));
    }
    evals.push(z_evals);

    let mut z_prod_evals = Vec::new();
    for x in eval_points.iter() {
        z_prod_evals.push(z_prod.evaluate(x));
    }
    evals.push(z_prod_evals);

    let mut q_r_evals = Vec::new();
    for x in eval_points.iter() {
        q_r_evals.push(q_z.evaluate(x));
    }   
    evals.push(q_r_evals);

    let mut q_range_evals = Vec::new();
    for x in eval_points.iter() {
        q_range_evals.push(q_range.evaluate(x));
    }   
    evals.push(q_range_evals);

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
    

    return (time_batched_commitments, time_batched_commitments2, evals, evals2, hash_coeffs, proof1, proof2);
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

// Converts commitments to Fr for hashing
fn convert_commitments_to_fr(commitments: Vec<Commitment<Bls12_381>>) -> Vec<Fr> {
    let mut ret = Vec::new();
    for commitment in commitments {
        let affine_rep = GAffine::from(commitment.0);
        let mut bits_x1 = affine_rep.x.into_bigint().to_bits_le();
        let mut bits_y1 = affine_rep.y.into_bigint().to_bits_le();

        let bits_x2 = bits_x1.split_off(bits_x1.len() / 2);
        let bits_y2 = bits_y1.split_off(bits_y1.len() / 2);

        ret.push(Fr::from_bigint(BigInteger::from_bits_le(&bits_x1)).unwrap());
        ret.push(Fr::from_bigint(BigInteger::from_bits_le(&bits_x2)).unwrap());
        ret.push(Fr::from_bigint(BigInteger::from_bits_le(&bits_y1)).unwrap());
        ret.push(Fr::from_bigint(BigInteger::from_bits_le(&bits_y2)).unwrap());
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

// Calculates Poseidon hash of commitments
fn get_poseidon_hash_of_commmitments(commitments: Vec<Commitment<Bls12_381>>, num_elements: usize) -> Vec<Fr> {
    return get_poseidon_hash(&convert_commitments_to_fr(commitments), num_elements);
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

    // Get PoseidonHash(LatticeHash(originalPhoto)) 
    // In practice, this value is directly given to the verifier. We only rederive it here 
    // for ease of programming
    let full_hash = calculate_full_hash(start);
    last = print_time_since(start, last, "calculate_full_hash done"); 
    let short_hash = get_poseidon_hash(&full_hash, 1)[0];

    // Hash edited photo to get gamma value
    let filename = get_filename("edited_");
    let input = Path::new(&filename);
    let val = try_digest(input).unwrap();
    let sha2561 = u128::from_str_radix(&val[0..32], 16).unwrap();
    let sha2562 = u128::from_str_radix(&val[32..64], 16).unwrap();

    let mut vals_to_hash = Vec::new();
    vals_to_hash.push(Fr::from(sha2561));
    vals_to_hash.push(Fr::from(sha2562));
    vals_to_hash.push(short_hash);
    let gamma = get_poseidon_hash(&vals_to_hash, 1)[0];
    last = print_time_since(start, last, "gamma generation done"); 

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
    let mut a_polys = Vec::new();
    for i in 0..HASH_LENGTH {
        let a = interpolate(a_vals_vec[i].clone(), domain);
        a_polys.push(a.coeffs);
    } 

    let time_batched_commitments = time_ck.batch_commit(&a_polys);

// ===================================================================================================================================

    // PROVER WORK
    // Create commitments, opening proofs, and claimed evaluations
    let (coms1, coms2, evals, evals2, prover_hash_coeffs, proof1, proof2) = eval_polynomials(domain, start, gamma, time_ck);
    // Create Groth16 proof to verify short_hash=PoseidonHash(full_hash) and linear_combo_hash = hash_coeffs \dot full_hash
    let proof = prove_poseidon_circuit(full_hash, prover_hash_coeffs.clone(), short_hash, evals2[1][2], pk);

    last = print_time_since(start, last, "PROVER TOOK");     

// ===================================================================================================================================

    // VERIFIER WORK

    // Rederive random coefficients and challenges
    let hash_coeffs = get_poseidon_hash_of_commmitments(coms1.clone(), HASH_LENGTH);
    let hashes = get_poseidon_hash_of_commmitments(coms2.clone(), 3);
    let alpha = hashes[0];
    let eta1 = hashes[1];
    let eta2 = hashes[2];

    // Re-generate eval_points
    let mut eval_points = Vec::new();
    eval_points.push(alpha);
    eval_points.push(domain.group_gen() * alpha);
    eval_points.push(domain.group_gen().pow(&[(D) as u64]));
    eval_points.push(domain.group_gen().pow(&[(PIXEL_RANGE) as u64]));
    eval_points.push(domain.group_gen().pow(&[(D + PIXEL_RANGE as usize) as u64])); 

    // Verify both sets of commitment evaluation proofs
    let verification_result = time_vk.verify_multi_points(
        &coms1,
        &eval_points,
        &evals,
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

    // Permutation Checks
    // Check (w_prod[omega*alpha] - w_prod[alpha](gamma + w[alpha])) * n_1[alpha] = q_w[alpha] * Z_H[alpha]
    assert!((evals[1][1] - evals[1][0] * (gamma + evals[0][0])) * n_1_of_alpha == evals[2][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check (v_prod[omega*alpha] - v_prod[alpha](gamma + v[alpha])) * n_1[alpha] = q_v[alpha] * Z_H[alpha]
    assert!((evals[4][1] - evals[4][0] * (gamma + evals[3][0])) * n_1_of_alpha == evals[5][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check (z_prod[omega*alpha] - z_prod[alpha](gamma + z[alpha])) * n_1[alpha] = q_z[alpha] * Z_H[alpha]
    assert!((evals[7][1] - evals[7][0] * (gamma + evals[6][0])) * n_1_of_alpha == evals[8][0] * domain.evaluate_vanishing_polynomial(alpha));
    // Check v_prod[omega^D] * w_prod[omega^PIXEL_RANGE] = z_prod[omega^{D + PIXEL_RANGE}]
    assert!(evals[4][2] * evals[1][3] == evals[7][4]);

    // Range Checks
    // Check n_1[alpha] * (z[omega*alpha] - z[alpha]) (1 - z[omega*alpha] - z[alpha]) = q_range[alpha] * Z_H[alpha]
    let dif = evals[6][1] - evals[6][0]; 
    assert!(n_1_of_alpha * dif * (Fr::from(1u64) - dif) == evals[9][0] * domain.evaluate_vanishing_polynomial(alpha));

    // Hash Value Checks
    // Check (h_sum[omega*alpha] - h_sum[alpha] - v[alpha] * a[alpha]) * n_1[alpha] =  q_h_sum[alpha] * Z_H[alpha]
    assert!((evals2[1][1] - evals2[1][0] - evals[3][0] * a.evaluate(&alpha)) * n_1_of_alpha  == evals2[2][0] * domain.evaluate_vanishing_polynomial(alpha));
 
    // Verify Groth16 proof
    let linear_combo_hash = evals2[1][2];
    verify_poseidon_circuit(proof, vk, hash_coeffs, short_hash, linear_combo_hash);

    println!("{}", linear_combo_hash);
    println!("{}", short_hash);

    _ = print_time_since(start, last, "VERIFIER TOOK"); 

    let mem = proc_status::mem_usage().unwrap();
    println!("Mem usage in bytes: current={}, peak={}", mem.current, mem.peak);


}

