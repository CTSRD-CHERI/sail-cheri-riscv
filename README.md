# CHERI RISC-V Sail model
This repository contains an implementation of the CHERI extensions
for the RISCV architecture in [sail](http://github.com/rems-project/sail). It is designed to be used with the [sail-riscv](http://github.com/rems-project/sail-riscv)
model, which is included as a submodule. To checkout / build (assuming you have installed sail):
```
git clone --recurse-submodules https://github.com/CTSRD-CHERI/sail-cheri-riscv
cd sail-cheri-riscv
```
You can build either an ocaml or C emulator, or a special binary for use with [TestRIG](https://github.com/CTSRD-CHERI/TestRIG):
```
make ocaml_emulator/cheri_riscv_ocaml_sim_RV64
make c_emulator/cheri_riscv_sim_RV64
make c_emulator/cheri_riscv_rvfi_RV64
```

The
[sail-cheri-riscv-verif](https://github.com/CTSRD-CHERI/sail-cheri-riscv-verif/)
repository contains a number of SMT-checked properties of the compressed
capability helper functions.

## Building to Rocq

To build the Rocq code for CHERI RISCV you'll first need to install Sail and Coq-Sail from their repositories.
The following script sets up the opam environment.

```bash
# Tested with opam 2.2.1
opam switch create sail-cheri-riscv 4.14.1
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add coq 8.20.0
# Add sail, tested with commit 54574467c33b56673151a0ee720f5dd09e74ac0a
git clone https://github.com/rems-project/sail.git
cd sail
opam install .
cd ..
# Add coq-sail, tested with commit ae4cd3fa351bb1a696e43ef86d4d7eed3618f874
git clone https://github.com/rems-project/coq-sail.git
cd coq-sail
opam install .
```

Then simply run `make riscv_coq_build` from the sail-cheri-riscv repo directory.
It should print a lot of warnings and take some time to build.
If it fails, it may mean you didn't clone the directory with `--recurse-submodules`.
In this case try running `git submodule update --init` to initialize the sail-riscv dependency.

You'll find the generated definitions in `generated_definitions/coq/RV64/*.v`.
Despite not having `CHERI` in the path, it is indeed the CHERI definitions.
For reassurance search for `Capability` or a capability-aware instruction like `CJALR`.

## Funding

This software was developed by SRI International and the University of
Cambridge Computer Laboratory (Department of Computer Science and
Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and
under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA
SSITH research programme.

This software was developed within the Rigorous Engineering of
Mainstream Systems (REMS) project, partly funded by EPSRC grant
EP/K008528/1, at the Universities of Cambridge and Edinburgh.
