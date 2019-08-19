# Coq snapshot of the Sail CHERI-RISC-V model

To build the Coq model, clone a copy of the bbv library in the parent
directory (this was tested with commit `143c47b`) and build it.  Then
run the `./build` script.

This was made from commit `46f3ea9` using Sail commit `4172e4cc` and
the changes in the patch file.  (The patch to `setCapBounds` deals
with a type printing problem in the Coq backend, and the change to
`haveXcheri` works around a limitation with register accesses in
mappings in Sail.)  The version of sail-riscv used had `eafbb79`
cherry-picked to match the changes to barriers in Sail.
