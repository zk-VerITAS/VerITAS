use plonky2::field::polynomial::{PolynomialCoeffs, PolynomialValues};
use plonky2::fri::oracle::PolynomialBatch;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::field::types::Field;
use plonky2::field::extension::Extendable;
use plonky2::util::timing::TimingTree;
use plonky2::field::fft::fft_root_table;
use plonky2::util::{log2_ceil, log2_strict};
use core::cmp::max;
use std::time::{SystemTime, UNIX_EPOCH};
use std::io::{BufRead, BufReader};
use rayon::prelude::*;
use plonky2::plonk::config::GenericHashOut;
use sha256::digest;
 use std::fs::File;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::fri::structure::FriPolynomialInfo;
use plonky2::fri::structure::FriInstanceInfo;
use plonky2::fri::structure::FriBatchInfo;
use plonky2::iop::challenger::Challenger;
use plonky2::fri::structure::FriOracleInfo;
use plonky2::fri::reduction_strategies::FriReductionStrategy;
use plonky2::fri::FriConfig;
use plonky2::fri::structure::FriOpeningBatch;
use plonky2::fri::structure::FriOpenings;
use plonky2::fri::verifier::verify_fri_proof;
use plonky2::field::extension::quadratic::QuadraticExtension;
use plonky2::field::types::PrimeField64;
use plonky2::field::types::Field64;
use plonky2::hash::merkle_tree::MerkleCap;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::field::fft::FftRootTable;
use plonky2::fri::proof::FriProof;

static PIXELS : usize = 14;
static EXPONENT : u32 = 3;
const DEGREE : usize = 1 << 5;
static PIXEL_RANGE : i32 = 2_i32.pow(EXPONENT);
const HASH_LENGTH : usize = 128;
const BATCH_SIZE : usize = 32;
const X : u128 = 3091352403337663489;
const A_CONSTANT : u128 = 3935559000370003845;
const C_CONSTANT : u128 = 2691343689449507681;
const USE_ZK : bool = false;

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;

fn print_time_since(start: u128, last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!("{:?}; time since start {:?}; time since last check: {:?}", tag, (now - start) as f32 / 60000.0, (now - last) as f32 / 60000.0); 
    return now;
}


fn get_filename(prefix: &str) -> String {
    let mut filename = prefix.to_owned();
    filename.push_str("image_");
    filename.push_str(&PIXELS.to_string());
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
fn get_sha256_of_commitments(merkle_cap: &MerkleCap<F, PoseidonHash>, instance_hash: &str, num_elements: usize) -> Vec<F> {
    let mut byte_vec = Vec::new();

    for hash in &merkle_cap.0 {
        let h = hash.to_vec();
        for elem in h {
            byte_vec.append(&mut elem.to_canonical_u64().to_le_bytes().to_vec());
        }
    }

    let s = format!("{:?}{:?}", &byte_vec, instance_hash);
    let mut val = digest(s);

    let mut ret = Vec::new();

    for _ in 0..num_elements/4 {
        let sha2561 = u64::from_str_radix(&val[0..16], 16).unwrap() % F::ORDER;
        ret.push(F::from_canonical_u64(sha2561));
        let sha2562 = u64::from_str_radix(&val[16..32], 16).unwrap();
        ret.push(F::from_canonical_u64(sha2562));
        let sha2563 = u64::from_str_radix(&val[32..48], 16).unwrap();
        ret.push(F::from_canonical_u64(sha2563));
        let sha2564 = u64::from_str_radix(&val[48..64], 16).unwrap();
        ret.push(F::from_canonical_u64(sha2564));
        val = digest(val);
    }
    
    return ret;
}

fn read_a_merkle_caps(batch: usize) -> MerkleCap<F, PoseidonHash>{
    let mut filename = "A_256_".to_owned();
    filename.push_str(&PIXELS.to_string());
    filename.push_str("_");
    filename.push_str(&EXPONENT.to_string());
    filename.push_str("_");
    filename.push_str(&batch.to_string());
    filename.push_str(".txt");

    let mut cap_hashes = Vec::new();
    let f = File::open(filename).expect("Unable to open file");
    let f = BufReader::new(f);
    for line in f.lines() {
        let line = line.expect("Unable to read line");
        let first_last_off: &str = &line[1..line.len() - 1];
        let parts = first_last_off.split(", ");
        let mut cap_hash = Vec::new();
        for part in parts {
            cap_hash.push(F::from_canonical_u64(part.parse::<u64>().unwrap()));
        }
        let hash = HashOut::from_vec(cap_hash);
        cap_hashes.push(hash);
    }
    let mut cap = MerkleCap::default();
    cap.0 = cap_hashes;
    return cap;
}

fn get_fri_config(rate_bits: usize, cap_height: usize) -> FriConfig {
    return FriConfig {
        rate_bits: rate_bits,
        cap_height: cap_height,
        proof_of_work_bits: 16,
        reduction_strategy: FriReductionStrategy::ConstantArityBits(4, 5),
        num_query_rounds: 28,
    };
}

fn prove_one(start: u128, old_last: u128, rate_bits: usize, cap_height: usize, omega: F, fft_root_table: &FftRootTable<F>) 
-> (FriOpenings<F, D>, [MerkleCap<GoldilocksField, PoseidonHash>; 3], FriProof<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, D>, QuadraticExtension<F>, u128)  {
    let mut last = old_last;
    // w_vals = [0, 1,...,PIXEL_RANGE - 1]
    let mut w_vals = Vec::new();
    for i in 0..PIXEL_RANGE {
        let i_in_fr = GoldilocksField(i as u64);
        w_vals.push(i_in_fr);
    }

    let mut w_vals = Vec::new();
    for i in 0..PIXEL_RANGE {
        let i_in_fr = GoldilocksField(i as u64);
        w_vals.push(i_in_fr);
    }

    for _ in 0..DEGREE - (PIXEL_RANGE as usize) {
        w_vals.push(F::ZERO);
    }

    // w[X] = poly(w_vals)
    let w = PolynomialValues::new(w_vals).ifft();

    last = print_time_since(start, last, "w interpolation done"); 

    // v_vals = [pixel_0,...,pixel_{D-1}]
    let mut v_vals = Vec::new();
    // z_vals = [sort(v || w)]
    let mut z_vals = Vec::new();

    // reading in photo pixels...
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = GoldilocksField(i as u64); 
        v_vals.push(v_point);
        z_vals.push(i);
    }

    for _ in 0..DEGREE - PIXELS {
        v_vals.push(F::ZERO);
    }

    for i in 0..PIXEL_RANGE {
        z_vals.push(i);
    }

    // pad z_vals so that [z[omega*x] - z[x][1 - (z[omega*x] - z[x])] = 0 still holds true
    let z_vals_length = z_vals.len();
    for _ in 0..DEGREE - z_vals_length {
        z_vals.push(PIXEL_RANGE - 1);
    }
    z_vals.sort();

    let mut z_f_vals = Vec::new();
    for i in 0..z_vals.len() {
        z_f_vals.push(GoldilocksField(z_vals[i] as u64));
    }
    

    // v[X] = poly(v_vals)
    let v = PolynomialValues::new(v_vals).ifft();
    // z[X] = poly(z_vals)
    let z = PolynomialValues::new(z_f_vals.clone()).ifft();
    last = print_time_since(start, last, "z and v interpolation done"); 

    

    let mut values_vec_0 = Vec::new();
    values_vec_0.push(w.clone());
    values_vec_0.push(v.clone());
    values_vec_0.push(z.clone());

    last = print_time_since(start, last, "polynomial push done"); 

    let commit0 = PolynomialBatch::<F, C, D>::from_coeffs(
            values_vec_0,
            rate_bits,
            USE_ZK,
            cap_height,
            &mut TimingTree::default(),
            Some(&fft_root_table),
        );
        
    last = print_time_since(start, last, "commit0 done"); 
    let gamma = get_sha256_of_commitments(&commit0.merkle_tree.cap, "", 4)[0];

    last = print_time_since(start, last, "gamma done"); 

    // Permutation argument
    // We want to prove:
    //           product_{i=0}^{D-1}(v_i + gamma) * product_{i=0}^{PIXEL_RANGE-1}(w_i + gamma) = product_{i=0}^{D + PIXEL_RANGE - 1}(z_i + gamma) 
    // where v holds the image pixels, w is the range that the pixel values must lie in [0, PIXEL_RANGE-1],
    // and z is the sorted concatentation of v and w

    let mut values_vec_1 = Vec::new();

    // w_prod_vals = [1, (gamma), [(gamma)(1 + gamma)],...,[(gamma)...(PIXEL_RANGE - 1 + gamma)]]
    let mut w_prod_vals = Vec::new();
    let mut product = F::ONE;
    w_prod_vals.push(product);

    for i in 0..PIXEL_RANGE {
        let i_in_fr = GoldilocksField(i as u64);
        product *= i_in_fr + gamma;
        w_prod_vals.push(product);
    }

    let w_prod_vals_len = w_prod_vals.len();
    for _ in 0..DEGREE - w_prod_vals_len {
        product *= gamma;
        w_prod_vals.push(product);
    }
    
    // w_prod_omega_vals = [(gamma), [(gamma)(1 + gamma)],...,[(gamma)...(PIXEL_RANGE + gamma)], 1]
    let mut w_prod_omega_vals = Vec::new();
    for i in 1..w_prod_vals.len() {
        w_prod_omega_vals.push(w_prod_vals[i]);
    }
    w_prod_omega_vals.push(w_prod_vals[0]);

    let w_prod = PolynomialValues::new(w_prod_vals).ifft();

    let w_prod_omega = PolynomialValues::new(w_prod_omega_vals).ifft();

    last = print_time_since(start, last, "w_prod and w_prod_omega interpolation done"); 

    let mut n_1_coeffs = Vec::new();
    n_1_coeffs.push(omega.exp_u64((DEGREE - 1) as u64));
    n_1_coeffs.push(F::ZERO - F::ONE);
    
    let n_1 = PolynomialCoeffs::from(n_1_coeffs);
    println!("n_1 eval {:?}", n_1.eval(omega.exp_u64((DEGREE - 1) as u64)));
    last = print_time_since(start, last, "n_1 interpolation done"); 

    let mut gamma_coeffs = Vec::new();
    gamma_coeffs.push(gamma);
    let gamma_poly = PolynomialCoeffs::from(gamma_coeffs);

    // let (q_w, r_w) = (&(&w_prod_omega - &(&w_prod * &(&gamma_poly + &w))) * &n_1).div_rem(&vanishing_poly);
    // assert!(r_w.is_zero());
    let sum = &(&w_prod_omega - &(&w_prod * &(&gamma_poly + &w))) * &n_1;
    let q_w = PolynomialCoeffs::new(sum.coeffs[0..DEGREE].to_vec());
    // assert!(q_fake == q_w);
    last = print_time_since(start, last, "q_w division done"); 

    // Will commit to w_prod[X], q_w[X]
    values_vec_1.push(w_prod);
    values_vec_1.push(q_w);

    // v_prod_vals = [1, (pixel_0 + gamma), [(pixel_0 + gamma)(pixel_1 + gamma)],...,[(pixel_0 + gamma)...(pixel_{D-1} + gamma)]]
    let mut v_prod_vals = Vec::new();
    let mut product = F::ONE;
    v_prod_vals.push(product);

    // reading in photo pixels...
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = GoldilocksField(i as u64); 

        product *= v_point + gamma;
        v_prod_vals.push(product);
    }

    for _ in 0..DEGREE - PIXELS - 1 {
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
    let v_prod = PolynomialValues::from(v_prod_vals).ifft();

    // v_prod_omega[X] = v_prod[omega*X]
    let v_prod_omega = PolynomialValues::from(v_prod_omega_vals).ifft(); 

    last = print_time_since(start, last, "v_prod and v_prod_omega interpolation done"); 

    // q_v[X] = (v_prod[omega * X] - (v_prod[X] * (gamma + v[X]))) * n_1[X] / Z_H[X]
    // let (q_v, r_v) = (&(&v_prod_omega - &(&v_prod * &(&gamma_poly + &v))) * &n_1).div_rem(&vanishing_poly);
    let sum = &(&v_prod_omega - &(&v_prod * &(&gamma_poly + &v))) * &n_1;
    let q_v = PolynomialCoeffs::new(sum.coeffs[0..DEGREE].to_vec());
    // assert!(q_fake == q_v);
    // assert!(r_v.is_zero());

    last = print_time_since(start, last, "q_v division done"); 

    // Will commit to v_prod[X], q_v[X]
    values_vec_1.push(v_prod);
    values_vec_1.push(q_v);

    // z_prod_vals = [1, z_vals_0 + gamma, [(z_0 + gamma)(z_vals_1 + gamma)],...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)]]
    let mut z_prod_vals = Vec::new();
    let mut product = F::ONE;
    z_prod_vals.push(product);
    for i in 0..z_f_vals.len() - 1 {
        product *= z_f_vals[i] + gamma;
        z_prod_vals.push(product);
    }

    // Range argument
    // We want to prove for the z constructed above that:
    //      (z[X] - z[omega*X])(1 - (z[X] - z[omega*X]) = 0 mod Z_H[X]

    // z_omega_vals = [z_vals_0 + gamma,...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)], 1]
    let mut z_omega_vals = Vec::new();
    for i in 1..z_vals.len() {
        z_omega_vals.push(z_f_vals[i]);
    }
    z_omega_vals.push(z_f_vals[0]);

    // z_prod_omega_vals = [z_vals_0 + gamma, [(z_vals_0 + gamma)(z_vals_1 + gamma)],...,[(z_vals_0 + gamma)...(z_vals_{PIXEL_RANGE + D - 1} + gamma)], 1]
    let mut z_prod_omega_vals = Vec::new();
    for i in 1..z_prod_vals.len() {
        z_prod_omega_vals.push(z_prod_vals[i]);
    }
    z_prod_omega_vals.push(z_prod_vals[0]);

    // for all i \in [1, PIXEL_RANGE + D], z_prod[omega^i] = \prod_{j=0}^{i-1}(z_j + gamma)
    let z_prod = PolynomialValues::from(z_prod_vals).ifft();

    // z_prod_omega[X] = z_prod[omega*X]
    let z_prod_omega = PolynomialValues::from(z_prod_omega_vals).ifft();
    last = print_time_since(start, last, "z_prod and z_prod_omega interpolation done"); 

    // q_z[X] = (z_prod[omega * X] - (z_prod[X] * (gamma + z[X]))) * n_1[X] / Z_H[X]
    // let (q_z, r_z) = (&(&z_prod_omega - &(&z_prod * &(&gamma_poly + &z))) * &n_1).div_rem(&vanishing_poly);
    let sum = &(&z_prod_omega - &(&z_prod * &(&gamma_poly + &z))) * &n_1;
    let q_z = PolynomialCoeffs::new(sum.coeffs[0..DEGREE].to_vec());
    // assert!(q_fake == q_z);
    // assert!(r_z.is_zero());
    last = print_time_since(start, last, "q_z division done"); 

    let z_omega = PolynomialValues::from(z_omega_vals).ifft();

    let mut one_coeffs = Vec::new();
    one_coeffs.push(F::ONE);
    
    let one = PolynomialCoeffs::from(one_coeffs);
    last = print_time_since(start, last, "one interpolation done"); 

   
    let sum = &(&(&z_omega - &z) * &(&one - &(&z_omega - &z))) * &n_1;
    let q_range = PolynomialCoeffs::new(sum.coeffs[0..DEGREE].to_vec());

   last = print_time_since(start, last, "q_range division done"); 

    // Will commit to z_prod[X], q_z[X], q_range[X]
    values_vec_1.push(z_prod);
    values_vec_1.push(q_z);
    values_vec_1.push(q_range);

    let commit1 = PolynomialBatch::<F, C, D>::from_coeffs(
            values_vec_1,
            rate_bits,
            USE_ZK,
            cap_height,
            &mut TimingTree::default(),
            Some(&fft_root_table),
    );

    last = print_time_since(start, last, "commit1 done"); 

    // Now we prove knowledge of actual hash value (Section 5.5) 
    // Want to generate a[X] and prove that Equation 11 in Section 5.5 holds for
    // this a[X] and the v[X] generated above

    // Use commitments to generate random coefficients [r_0,...,r_{HASH_LENGTH-1}]
    // for random linear combination of sum checks
    let hash_coeffs = get_sha256_of_commitments(&commit1.merkle_tree.cap, "", HASH_LENGTH);

    // Let A be the public hashing matrix (we will generate it with a PRG)
    // a_vals = [\sum_{i=0}{HASH_LENGTH-1}r_i * A_{i, 0},...,\sum_{i=0}{HASH_LENGTH-1}r_i * A_{i, D - 1}]
    let mut a_vals = Vec::new();

    // h_sum_vals = [0, v_vals_0 * a_vals_0 ,..., \sum_{i=0}^{D - 1} v_vals_0 * a_vals_0]
    let mut h_sum_vals = Vec::new();

    // h_sum_omega_vals = [\sum_{i=0}^{1} v_vals_0 * a_vals_0,...,\sum_{i=0}^{D - 1} v_vals_0 * a_vals_0, v_vals_0 * a_vals_0]
    let mut h_sum_omega_vals = Vec::new();
    h_sum_vals.push(F::ZERO);
    let mut sum = F::ZERO;

    let mut x = X;

    // Re-read in pixels
    let file = read_photo("orig_");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<i32>().unwrap();

        let v_point = GoldilocksField(i as u64); 

        let mut a_point = F::ZERO; 
        for j in 0..hash_coeffs.len() {
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff; 
            let x1 = x >> 32;
            x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff; 
            let x2 = ((x & 0xffffffff00000000) + x1) & 0xffffffffffffffff;

            a_point += F::from_canonical_u64(u64::try_from(x2).unwrap() % F::ORDER) * hash_coeffs[j];
        }
        a_vals.push(a_point);

        sum += v_point * a_point;
        h_sum_vals.push(sum);
        h_sum_omega_vals.push(sum);
    }

    let a_vals_length = a_vals.len();
    for _ in 0..DEGREE - a_vals_length {
        a_vals.push(F::ZERO);
    }

    for _ in 0..DEGREE - PIXELS - 1 {
        h_sum_vals.push(sum);
        h_sum_omega_vals.push(sum);
    }
    h_sum_omega_vals.push(F::ZERO);


    // for all i \in [0, D - 1], a[omega^i] = \sum_{j=0}{HASH_LENGTH-1}r_j * A_{j, i}
    let a = PolynomialValues::from(a_vals).ifft(); 

    // for all i \in [0, D], h_sum[omega^i] = \sum_{j=0}^{i} v_vals_j * a_vals_j
    let h_sum = PolynomialValues::from(h_sum_vals).ifft(); 

    // h_sum_omega[X] = h_sum[omega*X]
    let h_sum_omega = PolynomialValues::from(h_sum_omega_vals).ifft();

    last = print_time_since(start, last, "a, h_sum, h_sum_omega interpolation done"); 

    // q_h_sum[X] = (h_sum[omega*X] - h_sum[X] - (v[X] * a[X]))* n_1[X] / Z_H[X]
    // let (q_h_sum, r_h_sum) = (&(&(&h_sum_omega - &h_sum) - &(&v * &a))* &n_1).div_rem(&vanishing_poly);
    let sum = &(&(&h_sum_omega - &h_sum) - &(&v * &a))* &n_1;
    let q_h_sum = PolynomialCoeffs::new(sum.coeffs[0..DEGREE].to_vec());
    // assert!(r_h_sum.is_zero());    
    last = print_time_since(start, last, "q_h_sum interpolation done"); 

    // Second set of polynomials we commit to
    let mut values_vec_2 = Vec::new();

    // Will commit to a[X], h_sum[X], q_h_sum[X]
    // values_vec_2.push(a);
    values_vec_2.push(h_sum);
    values_vec_2.push(q_h_sum);

    let commit2 = PolynomialBatch::<F, C, D>::from_coeffs(
            values_vec_2,
            rate_bits,
            USE_ZK,
            cap_height,
            &mut TimingTree::default(),
            Some(&fft_root_table),
        );


    last = print_time_since(start, last, "commit2 done"); 

    let mut challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();

    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&commit0.merkle_tree.cap);
    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&commit1.merkle_tree.cap);
    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&commit2.merkle_tree.cap);

    for i in 0..HASH_LENGTH / BATCH_SIZE {
        let cap = read_a_merkle_caps(i);
        challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&cap);
    }

        

    let zeta = challenger.get_extension_challenge::<D>();

    let degree_bits = log2_strict(DEGREE);

    let g = <<PoseidonGoldilocksConfig as GenericConfig<D>>::F as Extendable<D>>::Extension::primitive_root_of_unity(degree_bits);

    assert!(zeta.exp_power_of_2(degree_bits) != <<PoseidonGoldilocksConfig as GenericConfig<D>>::F as Extendable<D>>::Extension::ONE);

    let commit0_polys = FriPolynomialInfo::from_range(
        0,
        0..commit0.polynomials.len(),
    );

    let commit1_polys = FriPolynomialInfo::from_range(
        1,
        0..commit1.polynomials.len(),
    );

    let commit2_polys = FriPolynomialInfo::from_range(
        2,
        0..commit2.polynomials.len(),
    );

    let all_polys = [commit0_polys, commit1_polys, commit2_polys].concat();


    let zeta_batch = FriBatchInfo {
        point: zeta,
        polynomials: all_polys.clone(),
    };

    // The Z polynomials are also opened at g * zeta.
    let zeta_next = g * zeta;
    let zeta_next_batch = FriBatchInfo {
        point: zeta_next,
        polynomials: all_polys.clone(),
    };

    let pixels = g.exp_u64((PIXELS) as u64);
    let pixels_batch = FriBatchInfo {
        point: pixels,
        polynomials: all_polys.clone(),
    };

    let pixel_range = g.exp_u64((PIXEL_RANGE) as u64);
    let pixel_range_batch = FriBatchInfo {
        point: pixel_range,
        polynomials: all_polys.clone(),
    };

    let pixels_plus_pixel_range = g.exp_u64((PIXELS + PIXEL_RANGE as usize) as u64);
    let pixels_plus_pixel_range_batch = FriBatchInfo {
        point: pixels_plus_pixel_range,
        polynomials: all_polys,
    };

    let openings = vec![zeta_batch, zeta_next_batch, pixels_batch, pixel_range_batch, pixels_plus_pixel_range_batch];


    let fri_oracles = vec![
            FriOracleInfo {
                num_polys: commit0.polynomials.len(),
                blinding: USE_ZK,
            },
            FriOracleInfo {
                num_polys: commit1.polynomials.len(),
                blinding: USE_ZK,
            },
            FriOracleInfo {
                num_polys: commit2.polynomials.len(),
                blinding: USE_ZK,
            }
        ];

    let instance = FriInstanceInfo {
        oracles: fri_oracles,
        batches: openings,
    };

    let fri_config = get_fri_config(rate_bits, cap_height); 

    let mut challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();

    let opening_proof = PolynomialBatch::<F, C, D>::prove_openings(
        &instance,
        &[
            &commit0,
            &commit1,
            &commit2
        ],
        &mut challenger,
        &fri_config.fri_params(degree_bits, true),
        &mut TimingTree::default(),
    );

    last = print_time_since(start, last, "openings commitment done"); 


    let merkle_caps = &[
        commit0.merkle_tree.cap.clone(),
        commit1.merkle_tree.cap.clone(),
        commit2.merkle_tree.cap.clone()
    ];

    let eval_commitment = |z: <<PoseidonGoldilocksConfig as GenericConfig<D>>::F as Extendable<D>>::Extension, c: &PolynomialBatch<F, C, D>| {
            c.polynomials
                .par_iter()
                .map(|p| p.to_extension::<D>().eval(z))
                .collect::<Vec<_>>()
    };

    let commit0_zeta_eval = eval_commitment(zeta, &commit0);
    let commit0_zeta_next_eval = eval_commitment(zeta_next, &commit0);
    let commit0_pixels_eval = eval_commitment(pixels, &commit0);
    let commit0_pixel_range_eval = eval_commitment(pixel_range, &commit0);
    let commit0_pixels_and_pixel_eval = eval_commitment(pixels_plus_pixel_range, &commit0);

    let commit1_zeta_eval = eval_commitment(zeta, &commit1);
    let commit1_zeta_next_eval = eval_commitment(zeta_next, &commit1);
    let commit1_pixels_eval = eval_commitment(pixels, &commit1);
    let commit1_pixel_range_eval = eval_commitment(pixel_range, &commit1);
    let commit1_pixels_and_pixel_eval = eval_commitment(pixels_plus_pixel_range, &commit1);

    let commit2_zeta_eval = eval_commitment(zeta, &commit2);
    let commit2_zeta_next_eval = eval_commitment(zeta_next, &commit2);
    let commit2_pixels_eval = eval_commitment(pixels, &commit2);
    let commit2_pixel_range_eval = eval_commitment(pixel_range, &commit2);
    let commit2_pixels_and_pixel_eval = eval_commitment(pixels_plus_pixel_range, &commit2);

    let zeta_batch = FriOpeningBatch {
        values: [
            commit0_zeta_eval.as_slice(),
            commit1_zeta_eval.as_slice(),
            commit2_zeta_eval.as_slice(),
        ].concat(),
    };
    
    let zeta_next_batch =  FriOpeningBatch {
        values: [
            commit0_zeta_next_eval.as_slice(),
            commit1_zeta_next_eval.as_slice(),
            commit2_zeta_next_eval.as_slice(),
        ].concat()
    };

    let pixels_batch = FriOpeningBatch {
        values: [
            commit0_pixels_eval.as_slice(),
            commit1_pixels_eval.as_slice(),
            commit2_pixels_eval.as_slice(),
        ].concat(),
    };

    let pixel_range_batch = FriOpeningBatch {
        values: [
            commit0_pixel_range_eval.as_slice(),
            commit1_pixel_range_eval.as_slice(),
            commit2_pixel_range_eval.as_slice(),
        ].concat(),
    };

    let pixels_plus_pixel_range_batch = FriOpeningBatch {
        values: [
            commit0_pixels_and_pixel_eval.as_slice(),
            commit1_pixels_and_pixel_eval.as_slice(),
            commit2_pixels_and_pixel_eval.as_slice(),
        ].concat(),
    };

    let fri_openings = FriOpenings {
        batches: vec![zeta_batch, zeta_next_batch, pixels_batch, pixel_range_batch, pixels_plus_pixel_range_batch],
    };


    last = print_time_since(start, last, "finished evaluating non-a stuff"); 
    
    return (fri_openings, merkle_caps.clone(), opening_proof, zeta, last);
}

fn prove_two(start: u128, old_last: u128, rate_bits: usize, cap_height: usize, fft_root_table: &FftRootTable<F>, zeta: QuadraticExtension<F>) -> 
(Vec<FriOpenings<F, D>>, Vec<FriProof<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher, D>>, Vec<QuadraticExtension<F>>) {
    let mut last = old_last;
    let mut all_a_fri_openings = Vec::new();
    let mut all_a_opening_proofs = Vec::new();

    let fri_config = get_fri_config(rate_bits, cap_height); 


    let eval_commitment = |z: <<PoseidonGoldilocksConfig as GenericConfig<D>>::F as Extendable<D>>::Extension, c: &PolynomialBatch<F, C, D>| {
            c.polynomials
                .par_iter()
                .map(|p| p.to_extension::<D>().eval(z))
                .collect::<Vec<_>>()
    };

 
    let mut a_all_zeta_evals = Vec::new();
    // do row commitments and openings
    for batch in 0..HASH_LENGTH / BATCH_SIZE {
        let mut a_vals_vec = Vec::new();

        for _ in 0..BATCH_SIZE {
            a_vals_vec.push(Vec::new());
        }

        let mut x = 3091352403337663489;
        for _ in 0..PIXELS {
            for j in 0..HASH_LENGTH {
                x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff; 
                let x1 = x >> 32;
                x = (A_CONSTANT * x + C_CONSTANT) & 0xffffffffffffffff; 
                let x2 = ((x & 0xffffffff00000000) + x1) & 0xffffffffffffffff;
                let rand = F::from_canonical_u64(u64::try_from(x2).unwrap() % F::ORDER);

                if j / BATCH_SIZE == batch {
                    a_vals_vec[j % BATCH_SIZE].push(rand);
                }
            }
        }

        let a_vals_length = a_vals_vec[0].len();
        for _ in 0..DEGREE -  a_vals_length {
            for i in 0..a_vals_vec.len() {
                a_vals_vec[i].push(F::ZERO);
            }
        }

        let mut polynomials_vec = Vec::new();
        for i in 0..BATCH_SIZE {
            let a = PolynomialValues::new(a_vals_vec[i].clone()).ifft();
            polynomials_vec.push(a);
        } 

        last = print_time_since(start, last, "a finished interpolating"); 

        let commit = PolynomialBatch::<F, C, D>::from_coeffs(
            polynomials_vec,
            rate_bits,
            false,
            4,
            &mut TimingTree::default(),
            Some(&fft_root_table),
        );

        last = print_time_since(start, last, "a finished committing"); 

        // A ROW OPENINGS
        let a_instance = generate_a_instance(zeta);

        let mut a_challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();

        let degree_bits = log2_strict(DEGREE);

        let a_opening_proof = PolynomialBatch::<F, C, D>::prove_openings(
            &a_instance,
            &[
                &commit
            ],
            &mut a_challenger,
            &fri_config.fri_params(degree_bits, true),
            &mut TimingTree::default(),
        );
        all_a_opening_proofs.push(a_opening_proof.clone());

        last = print_time_since(start, last, "a openings commitment done"); 

        let commit_zeta_eval = eval_commitment(zeta, &commit);
        a_all_zeta_evals = [a_all_zeta_evals, commit_zeta_eval.clone()].concat();

        let a_zeta_batch = FriOpeningBatch {
            values: [
                commit_zeta_eval.as_slice()
            ].concat(),
        };

        let a_fri_openings = FriOpenings {
            batches: vec![a_zeta_batch],
        };
        all_a_fri_openings.push(a_fri_openings);

        last = print_time_since(start, last, "a eval commitment done"); 
        
        last = print_time_since(start, last, "verification a eval proof done"); 
    }

    return (all_a_fri_openings, all_a_opening_proofs, a_all_zeta_evals);
}

fn get_instance(length_0 : usize, length_1 : usize, length_2 : usize, degree_bits : usize, zeta : QuadraticExtension<F>) -> FriInstanceInfo<F, D> {
    let g = <<PoseidonGoldilocksConfig as GenericConfig<D>>::F as Extendable<D>>::Extension::primitive_root_of_unity(degree_bits);
    let commit0_polys = FriPolynomialInfo::from_range(
        0,
        0..length_0,
    );

    let commit1_polys = FriPolynomialInfo::from_range(
        1,
        0..length_1,
    );

    let commit2_polys = FriPolynomialInfo::from_range(
        2,
        0..length_2,
    );

    let all_polys = [commit0_polys, commit1_polys, commit2_polys].concat();


    let zeta_batch = FriBatchInfo {
        point: zeta,
        polynomials: all_polys.clone(),
    };

    // The Z polynomials are also opened at g * zeta.
    let zeta_next = g * zeta;
    let zeta_next_batch = FriBatchInfo {
        point: zeta_next,
        polynomials: all_polys.clone(),
    };

    let pixels = g.exp_u64((PIXELS) as u64);
    let pixels_batch = FriBatchInfo {
        point: pixels,
        polynomials: all_polys.clone(),
    };

    let pixel_range = g.exp_u64((PIXEL_RANGE) as u64);
    let pixel_range_batch = FriBatchInfo {
        point: pixel_range,
        polynomials: all_polys.clone(),
    };

    let pixels_plus_pixel_range = g.exp_u64((PIXELS + PIXEL_RANGE as usize) as u64);
    let pixels_plus_pixel_range_batch = FriBatchInfo {
        point: pixels_plus_pixel_range,
        polynomials: all_polys,
    };

    let openings = vec![zeta_batch, zeta_next_batch, pixels_batch, pixel_range_batch, pixels_plus_pixel_range_batch];

    let fri_oracles = vec![
            FriOracleInfo {
                num_polys: length_0,
                blinding: USE_ZK,
            },
            FriOracleInfo {
                num_polys: length_1,
                blinding: USE_ZK,
            },
            FriOracleInfo {
                num_polys: length_2,
                blinding: USE_ZK,
            }
        ];

    return FriInstanceInfo {
        oracles: fri_oracles,
        batches: openings,
    };
}

fn generate_a_instance(zeta: QuadraticExtension<F>) -> FriInstanceInfo<F,D> {
    let commit_polys = FriPolynomialInfo::from_range(
        0,
        0..BATCH_SIZE,
    );

    let a_all_polys = [commit_polys].concat();

    let zeta_a_batch: FriBatchInfo<F, D> = FriBatchInfo {
        point: zeta,
        polynomials: a_all_polys.clone(),
    };
    let a_openings = vec![zeta_a_batch];

    let a_fri_oracles = vec![
        FriOracleInfo {
            num_polys: BATCH_SIZE,
            blinding: false,
        }
    ];

    return FriInstanceInfo {
        oracles: a_fri_oracles,
        batches: a_openings,
    };
}

fn main() {    
    // FRI commitment constants
    let rate_bits = 2;
    let cap_height = 4;
    let max_quotient_degree_factor = 4;
    let degree_bits = log2_strict(DEGREE);
    let omega = F::primitive_root_of_unity(degree_bits);

    let max_fft_points = 1 << (degree_bits + max(rate_bits, log2_ceil(max_quotient_degree_factor)));
    let fft_root_table = fft_root_table(max_fft_points);

    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();

    // PROVER
    let (fri_openings, merkle_caps, opening_proof, zeta, mut last) = prove_one(start, start, rate_bits, cap_height, omega, &fft_root_table);
    let (all_a_openings, all_a_proofs, a_all_zeta_evals) = prove_two(start, last, rate_bits, cap_height, &fft_root_table, zeta);

    last = print_time_since(start, last, "all prover work done"); 

    // VERIFIER
    let mut challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();

    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&merkle_caps[0]);
    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&merkle_caps[1]);
    challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&merkle_caps[2]);

    for i in 0..HASH_LENGTH / BATCH_SIZE {
        let cap = read_a_merkle_caps(i);
        challenger.observe_cap::<<PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>(&cap);
    }
    let zeta = challenger.get_extension_challenge::<D>();

     // Verify all opening proofs
    let fri_config = get_fri_config(rate_bits, cap_height);
    let instance = get_instance(3, 7, 2, degree_bits, zeta);
    let mut challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();
    let fri_challenges = challenger.fri_challenges::<C, D>(
        &opening_proof.commit_phase_merkle_caps,
        &opening_proof.final_poly,
        opening_proof.pow_witness,
        degree_bits,
        &fri_config,
    );
    let res = verify_fri_proof::<F, C, D>(
        &instance,
        &fri_openings,
        &fri_challenges,
        &merkle_caps,
        &opening_proof,
        &fri_config.fri_params(degree_bits, true),
    );
    _ = res.unwrap();
    for i in 0..all_a_openings.len() {
        let mut a_challenger = Challenger::<F, <PoseidonGoldilocksConfig as GenericConfig<D>>::Hasher>::new();
        let a_fri_challenges = a_challenger.fri_challenges::<C, D>(
            &all_a_proofs[i].commit_phase_merkle_caps,
            &all_a_proofs[i].final_poly,
            all_a_proofs[i].pow_witness,
            degree_bits,
            &fri_config,
        );
        let a_instance = generate_a_instance(zeta);
        let cap = read_a_merkle_caps(i);
        let a_res = verify_fri_proof::<F, C, D>(
            &a_instance,
            &all_a_openings[i],
            &a_fri_challenges,
            &[cap],
            &all_a_proofs[i],
            &fri_config.fri_params(degree_bits, true),
        );
        _ = a_res.unwrap();
    }

    // Check polynomial equalities
    let mut vals = Vec::new();
    vals.push(F::ONE);
    for _ in 0..DEGREE - 1 {
        vals.push(F::ZERO);
    }
    vals.push(F::ZERO - F::ONE);
    let vanishing_poly = PolynomialCoeffs::new(vals);

    let mut n_1_coeffs = Vec::new();
    n_1_coeffs.push(omega.exp_u64((DEGREE - 1) as u64));
    n_1_coeffs.push(F::ZERO - F::ONE);
    
    let n_1 = PolynomialCoeffs::from(n_1_coeffs);

    let vanishing_poly_zeta_eval = vanishing_poly.to_extension::<D>().eval(zeta);
    let n_1_zeta_eval = n_1.to_extension::<D>().eval(zeta);

    let hash_coeffs = get_sha256_of_commitments(&merkle_caps[1], "", HASH_LENGTH);
    let mut a_zeta_eval = QuadraticExtension::from(F::ZERO);
    for i in 0..hash_coeffs.len() {
        a_zeta_eval += QuadraticExtension::from(hash_coeffs[i]) * a_all_zeta_evals[i];
    }

    let gamma = get_sha256_of_commitments(&merkle_caps[0], "", 4)[0];
    let gamma_ext = QuadraticExtension::from(gamma);

    // Check (w_prod[omega*zeta] - w_prod[zeta](gamma + w[zeta])) * n_1[zeta] = q_w[zeta] * Z_H[zeta]
    assert!((fri_openings.batches[1].values[3] - fri_openings.batches[0].values[3] * (gamma_ext  + fri_openings.batches[0].values[0])) * n_1_zeta_eval == fri_openings.batches[0].values[4] * vanishing_poly_zeta_eval);
    // Check (v_prod[omega*zeta] - v_prod[zeta](gamma + v[zeta])) * n_1[zeta] = q_v[zeta] * Z_H[zeta]
    assert!((fri_openings.batches[1].values[5] - fri_openings.batches[0].values[5] * (gamma_ext  + fri_openings.batches[0].values[1])) * n_1_zeta_eval == fri_openings.batches[0].values[6] * vanishing_poly_zeta_eval);
    // Check (z_prod[omega*alpha] - z_prod[alpha](gamma + z[alpha])) * n_1[alpha] = q_z[alpha] * Z_H[alpha]
    assert!((fri_openings.batches[1].values[7] - fri_openings.batches[0].values[7] * (gamma_ext  + fri_openings.batches[0].values[2])) * n_1_zeta_eval == fri_openings.batches[0].values[8] * vanishing_poly_zeta_eval);
    // Check v_prod[omega^D] * w_prod[omega^PIXEL_RANGE] = z_prod[omega^{D + PIXEL_RANGE}]
    assert!(fri_openings.batches[2].values[5] * fri_openings.batches[3].values[3] == fri_openings.batches[4].values[7]);

    // Range Checks
    // Check n_1[zeta] * (z[omega*zeta] - z[zeta]) (1 - z[omega*zeta] - z[zeta]) = q_range[zeta] * Z_H[zeta]
    let dif = fri_openings.batches[1].values[2] - fri_openings.batches[0].values[2]; 
    assert!(n_1_zeta_eval * dif * (QuadraticExtension::from(F::ONE) - dif) == fri_openings.batches[0].values[9] * vanishing_poly_zeta_eval);

    // Hash Value Checks
    // Check (h_sum[omega*zeta] - h_sum[zeta] - v[zeta] * a[zeta]) * n_1[zeta] =  q_h_sum[zeta] * Z_H[zeta]
    assert!((fri_openings.batches[1].values[10] - fri_openings.batches[0].values[10] - fri_openings.batches[0].values[1] * a_zeta_eval) * n_1_zeta_eval  ==  fri_openings.batches[0].values[11] * vanishing_poly_zeta_eval);
 
    //let mem = proc_status::mem_usage().unwrap();
    //println!("Mem usage in bytes: current={}, peak={}", mem.current, mem.peak);  
    _ = print_time_since(start, last, "all verification done"); 
    
}