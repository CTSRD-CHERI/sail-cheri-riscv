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
  // CHERI Capability Write.
  CW       : 6,
  // CHERI Capability Read Generation.
  CRG      : 5,
  reserved : 4 .. 0,
}
