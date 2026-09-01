/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function ext_pte_is_invalid(pte_flags : PTE_Flags, pte_ext : option(PTE_Ext)) -> bool =
  match pte_ext {
    // The RVY field must be 0 unless this is a leaf node.
    // YRGE clear reserves all but the Y bit.
    Some(pte_ext) => ((pte_ext[rvy] != zeros()) & pte_is_ptr(pte_flags)) |
                     (mstatus[YRGE] == 0b0 & (Mk_PTE_RVY(pte_ext[rvy])[reserved] != zeros())),
    None() => false,
  }
