/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* CHERI specific helpers */

val MEMr_tag = "read_tag_bool"  : bits(64) -> bool
val MEMw_tag = "write_tag_bool" : (bits(64) , bool) -> unit

val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1)
function MAX(n) = pow2(n) - 1

val not = {coq:"negb", _:"not"} : bool -> bool
