We rely on the KZG implementation from arkworks gemini (https://github.com/arkworks-rs/gemini). 
There were some compilation issues with the available version of Gemini when we were developing VerITAS,
so we implemented VerITAS from within the Gemini directory to get around compilation errors. VerITAS
is implemented in the examples directory, and we use genpic.py to generate test photos. All other code
was developed by the developers of Gemini; we include it here only for completeness.

Install the appropriate rust nightly version:

`rustup install nightly-2023-06-13`

`rustup default nightly-2023-06-13`


To create an example hash proof for D pixels of max value 2^E using VerITAS, run:

`python3 genpic.py orig D E`

`python3 genpic.py edited D E`

Then, in `veritas.rs`, edit line 45  to say `static D : usize = D;`, and edit line 46 to say, static 
`EXPONENT : u32 = E;`

Then, run:

`cargo run --example veritas`

To create an example hash proof for D pixels of max value 2^E using opt-VerITAS, in `generate-a-row-coms.rs`, 
edit line 48 to say `static D : usize = D;`, and edit line 49 to say, static `EXPONENT : u32 = E;`

Then, run:

`cargo run --example generate-a-row-coms`

This should create 8 files of the form `A_D_E_i.txt`.

Lastly, run: 

`cargo run --example opt-veritas`
