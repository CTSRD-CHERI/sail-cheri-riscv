/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Put the illegal instructions last to use their wildcard match. */

/* Wilcard match for 32-bit non-capmode encodings. */
union clause ast = NOT_CAPMODE : word
function clause execute(NOT_CAPMODE(s)) = {
  internal_error(__FILE__, __LINE__, "should be unreachable: execute(NOT_CAPMODE(" ^ BitStr(s) ^ "))");
  RETIRE_FAIL
}
mapping clause encdec_capmode = NOT_CAPMODE(s) <-> s
end encdec_capmode

/* Wilcard match for 16-bit non-capmode encodings. */
union clause ast = NOT_C_CAPMODE : half
function clause execute(NOT_C_CAPMODE(s)) = {
  internal_error(__FILE__, __LINE__, "should be unreachable: execute(NOT_C_CAPMODE(" ^ BitStr(s) ^ "))");
  RETIRE_FAIL
}
mapping clause encdec_compressed_capmode = NOT_C_CAPMODE(s) <-> s
end encdec_compressed_capmode
