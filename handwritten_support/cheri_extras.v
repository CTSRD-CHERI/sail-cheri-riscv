Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_mwords.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.

Definition write_ram {rv e} wk (addr : mword 64) size (v : mword (8 * size)) (tag : bool) : monad rv bool e := write_memt wk addr size v (bitU_of_bool tag).

Definition read_ram {rv e} rk (addr : mword 64) size (read_tag : bool) `{ArithFact (size >= 0)} : monad rv (mword (8 * size) * bool) e :=
  if read_tag then
    read_memt rk addr size >>= fun '(data, tag) =>
    bool_of_bitU_nondet tag >>= fun tag =>
    returnm (data, tag)
  else
    read_mem rk 64 addr size >>= fun data =>
    returnm (data, false).

Definition write_tag_bool {rv A E} (addr : mword A) tag : monad rv unit E :=
 read_memt Read_plain addr 16 >>= fun '(cap, _) =>
 write_memt Write_plain addr 16 cap (bitU_of_bool tag) >>= (fun _ => returnm tt).

Definition read_tag_bool {rv E} (addr : mword 64) : monad rv bool E :=
  read_memt (B := 128) Read_plain addr 16 >>= fun '(cap, tag) =>
  bool_of_bitU_nondet tag.
