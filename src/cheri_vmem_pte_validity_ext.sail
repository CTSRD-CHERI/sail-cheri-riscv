/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function ext_pte_is_invalid(pte_flags : PTE_Flags, pte_ext : option(PTE_Ext)) -> bool =
  match pte_ext {
    // The CRG/CW bits must be 0 unless this is a leaf node.
    Some(pte_ext) => (pte_ext[CW] != 0b0 | pte_ext[CRG] != 0b0) & not(pte_is_ptr(pte_flags)),
    None() => false,
  }
