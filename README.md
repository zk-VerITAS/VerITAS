To create an example hash proof for D pixels of max value 2^E using VerITAS, run:

`python3 genpic.py orig D E`

`python3 genpic.py edited D E`

Then, in `veritas.rs`, edit line 45  to say `static D : usize = D;`, and edit line 46 to say, static 
`EXPONENT : u32 = E;`

Then, run:

`cargo run --release --example veritas`

To create an example hash proof for D pixels of max value 2^E using opt-VerITAS, in `generate-a-row-coms.rs`, 
edit line ?? to say `static D : usize = D;`, and edit line 49 to say, static `EXPONENT : u32 = E;`

Then, run:

`cargo run --release --example generate-a-row-coms`

This should create 8 files of the form `A_D_E_i.txt`.

Lastly, run: 

`cargo run --release --example opt-veritas`

To create the editing proofs, you can run (and change the parameters within the corresponding files):

`cargo run --release --example blur`

`cargo run --release --example resize`

`cargo run --release --example crop`

`cargo run --release --example gray`
