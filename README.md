# CHERI RISC-V Sail model

This repository contains an implementation of the CHERI extensions
for the RISCV architecture in [Sail](http://github.com/rems-project/sail). It is designed to be used with the [sail-riscv](http://github.com/rems-project/sail-riscv)
model, which is included as a submodule. To checkout / build (assuming you have installed Sail):

```
git clone --recurse-submodules https://github.com/CHERI-Alliance/sail-cheri-riscv
cd sail-cheri-riscv
```

You can build either a C emulator:

```
make c_emulator/cheri_riscv_sim_RV64
```

## Relationship to other repos

The original CHERI RISC-V Sail repo is available [here](https://github.com/CTSRD-CHERI/sail-cheri-riscv). That repo implements [the CHERI ISAv9 specification](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/cheri-risc-v.html). This was the original specification developed by Cambridge University.

In 2024 a new specification was developed based on Codasip's experiences implementing CHERI ISAv9 in a commercial CPU. That specification is much simpler, omitting various experimental features and refining others. The new specification is [available here](https://riscv.github.io/riscv-cheri/). That is the specification implemented here.

You may notice that this repo also includes a lot of differences from [the main RISC-V model](https://github.com/riscv/sail-riscv) that are unrelated to CHERI, e.g. support for PMAs, Sdext/sdtrig, CLIC, etc. That is because we (Codasip) implemented both CHERI and those features in the same internal fork, and disentangling them requires some work.

The intention is that all of the non-CHERI changes will eventually be upstreamed to the main RISC-V repo, and then this repo will only contain CHERI changes. This may take some time.

## Status

The code compiles but some parts are a bit messy due to being moved from Codasip's internal repo. In particular:

* A lot of `plat_` and `sys_` callbacks have not been implemented in C and are hard-coded. This will be fixed once Sail's new config system is available (planned for early 2025).
* The Sdext/Sdtrig implementation is not especially clean and currently contains a lot of hard-coded behaviour that happens to match the chip it was written for (the specification allows an extremely wide range of behaviours).
