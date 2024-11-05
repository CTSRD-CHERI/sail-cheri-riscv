/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* accessors for default architectural addresses, for use from within instructions */

val get_arch_pc : unit -> xlenbits
function get_arch_pc() = PC

val get_next_pc : unit -> xlenbits
function get_next_pc() = nextPC

val set_next_pc : xlenbits -> unit
function set_next_pc(pc) = {
  /* could check for internal errors here on invalid pc */
  nextPC = convertInvalidAddr(pc)
}

val tick_pc : unit -> unit
function tick_pc() = {
  PCC = nextPCC;
  PC = nextPC
}

// Note that although the Sail model ignores the address part of PCC (it uses
// PC instead), we require it to be correct when this function is called so
// that convertInvalidAddr() behaves correctly.
val set_next_pcc : Capability -> unit
function set_next_pcc(pcc) = {
  // This is technically redundant for CJALR since it already bounds checks
  // the reduced address and unseals the cap.
  nextPCC = convertInvalidAddr(pcc);
}
