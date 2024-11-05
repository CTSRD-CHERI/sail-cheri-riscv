/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* register type */
type regtype = Capability

/* null cap */
let zero_reg : regtype = null_cap

/* register printer */
val RegStr : Capability -> string
function RegStr(r) = capToString(r)

/* conversions */

val regval_from_reg : regtype -> xlenbits
function regval_from_reg(r) = r.address

val regval_into_reg : xlenbits -> regtype
function regval_into_reg(v) = {null_cap with address = v}
