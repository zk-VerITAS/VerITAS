use plonky2::field::polynomial::{PolynomialValues};
use plonky2::fri::oracle::PolynomialBatch;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::field::types::Field;
use plonky2::util::timing::TimingTree;
use plonky2::field::fft::fft_root_table;
use plonky2::util::{log2_ceil, log2_strict};
use core::cmp::max;
use std::time::{SystemTime, UNIX_EPOCH};
use std::fs::File;
use plonky2::field::types::Field64;
use std::io::BufWriter;
use std::io::Write;

static PIXELS : usize = 14;
static EXPONENT : u32 = 3;
static HASH_LENGTH : usize = 128;
const BATCH_SIZE : usize = 32;
const DEGREE : usize = 1 << 5;

// lattice hash generation constants
const A_CONSTANT : u128 = 3935559000370003845;
const C_CONSTANT : u128 = 2691343689449507681;


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


fn main() {
    // FRI commitment constants
    let rate_bits = 2;
    let max_quotient_degree_factor = 4;
    let degree_bits = log2_strict(DEGREE);

    let max_fft_points = 1 << (degree_bits + max(rate_bits, log2_ceil(max_quotient_degree_factor)));

    let fft_root_table = fft_root_table(max_fft_points);


    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;
        
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

        last = print_time_since(start, last, "finished interpolating"); 

        let commit0 = PolynomialBatch::<F, C, D>::from_coeffs(
            polynomials_vec,
            rate_bits,
            false,
            4,
            &mut TimingTree::default(),
            Some(&fft_root_table),
        );

        let mut filename = "A_256_".to_owned();
        filename.push_str(&PIXELS.to_string());
        filename.push_str("_");
        filename.push_str(&EXPONENT.to_string());
        filename.push_str("_");
        filename.push_str(&batch.to_string());
        filename.push_str(".txt");

        last = print_time_since(start, last, "finished committing"); 

        let f = File::create(filename.clone()).expect("Unable to create file");
        let mut f = BufWriter::new(f);

        println!("commit0.merkle_tree.cap.len() {:?}", commit0.merkle_tree.cap.len());
        println!("commit0.merkle_tree.cap.0.len() {:?}", commit0.merkle_tree.cap.0[0].elements.len());
        for hash in &commit0.merkle_tree.cap.0 {
            writeln!(f, "{:?}", hash.elements);
        }
        drop(f);

        last = print_time_since(start, last, "finished writing commits"); 

    }   
    
}