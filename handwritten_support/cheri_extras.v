Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_mwords.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.

Definition write_tag_bool {rv A E} (addr : mword A) tag : monad rv unit E :=
  bind (bind (read_memt Read_plain addr 16)
             (fun '(cap, _) =>
                write_memt Write_plain addr 16 cap (bitU_of_bool tag)))
       (fun _ => Done tt).

Definition read_tag_bool {rv E} (addr : mword 64) : monad rv bool E :=
  bind (read_memt Read_plain addr 16)
       (fun '(cap, tag) => returnm (bool_of_bitU tag)). (* FIXME: need bool_of_bitU_nondet here? *)
