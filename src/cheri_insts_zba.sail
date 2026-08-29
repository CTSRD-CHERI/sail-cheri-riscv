/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = ZBA_Y_RTYPEUW : (regidx, regidx, regidx, bropw_zba_y)

mapping clause encdec = ZBA_Y_RTYPEUW(cs2, rs1, cd, RISCV_YSH1ADDUW)                      if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(cd) @ 0b0111011  if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec = ZBA_Y_RTYPEUW(cs2, rs1, cd, RISCV_YSH2ADDUW)                      if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(cd) @ 0b0111011  if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec = ZBA_Y_RTYPEUW(cs2, rs1, cd, RISCV_YSH3ADDUW)                      if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(cd) @ 0b0111011  if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec = ZBA_Y_RTYPEUW(cs2, rs1, cd, RISCV_YSH4ADDUW)                      if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b111 @ encdec_reg(cd) @ 0b0111011  if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64

mapping zba_y_rtypeuw_mnemonic : bropw_zba_y <-> string = {
  RISCV_YSH1ADDUW <-> "ysh1add.uw",
  RISCV_YSH2ADDUW <-> "ysh2add.uw",
  RISCV_YSH3ADDUW <-> "ysh3add.uw",
  RISCV_YSH4ADDUW <-> "ysh4add.uw",
}

mapping clause assembly = ZBA_Y_RTYPEUW(cs2, rs1, cd, op)
  <-> zba_y_rtypeuw_mnemonic(op) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: sh1234addyuw_32bit
 * Shift by _n_ and add unsigned word for address generation (YSH1ADD.UW,
 * YSH2ADD.UW, YSH3ADD.UW, YSH4ADD.UW)
 *
 * sh[1|2|3|4]addy.uw cd, rs1, cs2
 *
 * Increment the address field of cs2 by the unsigned word in rs1 shifted
 * left by _n_ bit positions and write the result to cd. The tag bit of
 * the output capability is 0 if cs2 did not have its tag set to 1, the
 * incremented address is outside cs2's Representable Range or cs2 is
 * sealed.
 */
function clause execute (ZBA_Y_RTYPEUW(cs2, rs1, cd, op)) = {
  let rs1_val = X(rs1);
  let cs2_val = Y(cs2);
  let shamt : range(0,4) = match op {
    RISCV_YSH1ADDUW => 1,
    RISCV_YSH2ADDUW => 2,
    RISCV_YSH3ADDUW => 3,
    RISCV_YSH4ADDUW => 4,
  };
  let result = incCapAddrChecked(cs2_val, zero_extend(rs1_val[31..0]) << shamt);
  Y(cd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_Y_RTYPE : (regidx, regidx, regidx, brop_zba_y)

mapping clause encdec = ZBA_Y_RTYPE(cs2, rs1, cd, RISCV_YSH1ADD)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
mapping clause encdec = ZBA_Y_RTYPE(cs2, rs1, cd, RISCV_YSH2ADD)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
mapping clause encdec = ZBA_Y_RTYPE(cs2, rs1, cd, RISCV_YSH3ADD)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled() & extensionEnabled(Ext_Zba)
mapping clause encdec = ZBA_Y_RTYPE(cs2, rs1, cd, RISCV_YSH4ADD)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b111 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled() & extensionEnabled(Ext_Zba) & xlen == 64

mapping zba_y_rtype_mnemonic : brop_zba_y <-> string = {
  RISCV_YSH1ADD <-> "ysh1add",
  RISCV_YSH2ADD <-> "ysh2add",
  RISCV_YSH3ADD <-> "ysh3add",
  RISCV_YSH4ADD <-> "ysh4add",
}

mapping clause assembly = ZBA_Y_RTYPE(cs2, rs1, cd, op)
  <-> zba_y_rtype_mnemonic(op) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: ysh1234add_32bit
 * Shift by _n_ and add for address generation (YSH1ADD, YSH2ADD, YSH3ADD, YSH4ADD)
 *
 * ysh[1|2|3|4]add cd, rs1, cs2
 *
 * Increment the address field of cs2 by rs1 shifted left by _n_ bit
 * positions and write the result to cd. The tag bit of the output
 * capability is 0 if cs2 did not have its tag set to 1, the incremented
 * address is outside cs2 's Representable Range or cs2 is sealed.
 */
function clause execute (ZBA_Y_RTYPE(cs2, rs1, cd, op)) = {
  let rs1_val = X(rs1);
  let cs2_val = Y(cs2);
  let shamt : range(0,4) = match op {
    RISCV_YSH1ADD => 1,
    RISCV_YSH2ADD => 2,
    RISCV_YSH3ADD => 3,
    RISCV_YSH4ADD => 4,
  };
  let result = incCapAddrChecked(cs2_val, rs1_val << shamt);
  Y(cd) = result;
  RETIRE_SUCCESS
}
