/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/*
 * We add a separate capability-mode encdec clause to handle encodings that overlap
 * with baseline RISC-V encodings.
 */
val encdec_capmode : ast <-> bits(32)
scattered mapping encdec_capmode

val encdec_compressed_capmode : ast <-> bits(16)
scattered mapping encdec_compressed_capmode
