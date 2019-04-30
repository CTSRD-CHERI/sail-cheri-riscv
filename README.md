# CHERI RISCV Sail model
This repository contains an implementation of the CHERI extensions
for the RISCV architecture in [sail](http://higtbu.com/rems-project/sail). It is designed to be used with the [sail-riscv](http://github.com/rems-project/sail-riscv)
model, which is included as a submodule. To checkout / build (assuming you have installed sail):
```
git clone --recurse-submodules https://github.com/rems-project/sail-cheri-riscv
cd sail-cheri-riscv
```
You can build either an ocaml or C emulator, or a special binary for use with [TestRIG](https://github.com/CTSRD-CHERI/TestRIG):
```
make ocaml_emulator/riscv_ocaml_sim_RV64
make c_emulator/riscv_sim_RV64
make c_emulator/riscv_rvfi
```
