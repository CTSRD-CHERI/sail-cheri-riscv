/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

bitfield PTE_Ext : pte_ext_bits = {
  // NAPOT page table entry.
  N        : 9,
  // Page based memory types.
  PBMT     : 8 .. 7,
  res_hi   : 6 .. 5,
  // CHERI Capability Write.
  CRW      : 4,
  // CHERI Capability Read Generation.
  CRG      : 3,
  // CHERI Capability Dirty.
  CD       : 2,
  res_lo   : 1 .. 0,
}
