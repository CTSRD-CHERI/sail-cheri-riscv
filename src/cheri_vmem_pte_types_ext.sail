/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// Interpretation of CHERI PTE bits when Svyrg present and enabled
bitfield PTE_RVY_SVYRG : bits(4) = {
  // CHERI Capability Dirty
  YD  : 3,
  // CHERI Capability Write
  YW  : 2,
  // CHERI Capability Read Generation
  YRG : 1,
  // CHERI Capability Read
  YR  : 0,
}

// Interpretation of CHEIR PTE bits without Svyrg
bitfield PTE_RVY : bits(4) = {
  // CHERI Capability Access
  Y        : 3,
  reserved : 2..0,
}

bitfield PTE_Ext : pte_ext_bits = {
  // NAPOT page table entry.
  N        : 9,
  // Page based memory types.
  PBMT     : 8 .. 7,
  res_hi   : 6 .. 5,
  rvy      : 4 .. 1,
  res_lo   : 0,
}
