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

## Funding

This software was developed by SRI International and the University of
Cambridge Computer Laboratory (Department of Computer Science and
Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and
under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA
SSITH research programme.

This software was developed within the Rigorous Engineering of
Mainstream Systems (REMS) project, partly funded by EPSRC grant
EP/K008528/1, at the Universities of Cambridge and Edinburgh.
