/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = ZBA_RTYPEUW_capmode : (regidx, regidx, regidx, bropw_zba)

mapping clause encdec_capmode = ZBA_RTYPEUW_capmode(cs2, rs1, cd, RISCV_ADDUW)    if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0000100 @ cs2 @ rs1 @ 0b000 @ cd @ 0b0111011                              if extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec_capmode = ZBA_RTYPEUW_capmode(cs2, rs1, cd, RISCV_SH1ADDUW) if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b010 @ cd @ 0b0111011                              if extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec_capmode = ZBA_RTYPEUW_capmode(cs2, rs1, cd, RISCV_SH2ADDUW) if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b100 @ cd @ 0b0111011                              if extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec_capmode = ZBA_RTYPEUW_capmode(cs2, rs1, cd, RISCV_SH3ADDUW) if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b110 @ cd @ 0b0111011                              if extensionEnabled(Ext_Zba) & xlen == 64

mapping clause assembly = ZBA_RTYPEUW_capmode(cs2, rs1, cd, op)
  <-> zba_rtypeuw_mnemonic(op) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: sh123adduw_32bit capmode
 * Shift by _n_ and add unsigned word for address generation (SH1ADD.UW,
 * SH2ADD.UW, SH3ADD.UW)
 *
 * sh[1|2|3]add.uw cd, rs1, cs2
 *
 * Increment the address field of cs2 by the unsigned word in rs1 shifted
 * left by _n_ bit positions and write the result to cd. The tag bit of
 * the output capability is 0 if cs2 did not have its tag set to 1, the
 * incremented address is outside cs2's Representable Range or cs2 is
 * sealed.
 */
/*
 * insnref: adduw_32bit capmode
 * Add unsigned word for address generation
 *
 * add.uw cd, rs1, cs2
 *
 * Increment the address field of cs2 by the unsigned word in rs1. Clear
 * the tag if the resulting capability is unrepresentable or cs2 is
 * sealed.
 */
function clause execute (ZBA_RTYPEUW_capmode(cs2, rs1, cd, op)) = {
  let rs1_val = X(rs1);
  let cs2_val = C(cs2);
  let shamt : range(0,3) = match op {
    RISCV_ADDUW    => 0,
    RISCV_SH1ADDUW => 1,
    RISCV_SH2ADDUW => 2,
    RISCV_SH3ADDUW => 3,
  };
  let result = incCapAddrChecked(cs2_val, zero_extend(rs1_val[31..0]) << shamt);
  C(cd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_SH4ADDUW : (regidx, regidx, regidx)
union clause ast = ZBA_SH4ADDUW_capmode : (regidx, regidx, regidx)

mapping clause encdec = ZBA_SH4ADDUW(cs2, rs1, cd)                 if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b111 @ cd @ 0b0111011               if extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec_capmode = ZBA_SH4ADDUW_capmode(cs2, rs1, cd) if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b111 @ cd @ 0b0111011               if extensionEnabled(Ext_Zba) & xlen == 64

mapping clause assembly = ZBA_SH4ADDUW(rs2, rs1, rd)
  <-> "sh4add.uw" ^ spc() ^     reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = ZBA_SH4ADDUW_capmode(cs2, rs1, cd)
  <-> "sh4add.uw" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: sh4adduw_32bit intmode
 * Shift by 4 and add unsigned words for address generation (SH4ADD.UW)
 *
 * sh4add.uw rd, rs1, rs2
 *
 * Increment rs2 by the unsigned word in rs1 shifted left by 4 bit
 * positions and write the result to rd.
 */
function clause execute (ZBA_SH4ADDUW(rs2, rs1, rd)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let shamt = 4;
  let result : xlenbits = (zero_extend(rs1_val[31..0]) << shamt) + rs2_val;
  X(rd) = result;
  RETIRE_SUCCESS
}

/*!
 * insnref: sh4adduw_32bit capmode
 * Shift by 4 and add unsigned words for address generation (SH4ADD.UW)
 *
 * sh4add.uw cd, rs1, cs2
 *
 * Increment the address field of cs2 by the unsigned word in rs1 shifted
 * left by 4 bit positions and write the result to cd. The tag bit of the
 * output capability is 0 if cs2 did not have its tag set to 1, the
 * incremented address is outside cs2's Representable Range or cs2 is
 * sealed.
 */
function clause execute (ZBA_SH4ADDUW_capmode(cs2, rs1, cd)) = {
  let rs1_val = X(rs1);
  let cs2_val = C(cs2);
  let shamt = 4;
  let result = incCapAddrChecked(cs2_val, zero_extend(rs1_val[31..0]) << shamt);
  C(cd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_RTYPE_capmode : (regidx, regidx, regidx, brop_zba)

mapping clause encdec_capmode = ZBA_RTYPE_capmode(cs2, rs1, cd, RISCV_SH1ADD) if extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ cs2 @ rs1 @ 0b010 @ cd @ 0b0110011                          if extensionEnabled(Ext_Zba)
mapping clause encdec_capmode = ZBA_RTYPE_capmode(cs2, rs1, cd, RISCV_SH2ADD) if extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ cs2 @ rs1 @ 0b100 @ cd @ 0b0110011                          if extensionEnabled(Ext_Zba)
mapping clause encdec_capmode = ZBA_RTYPE_capmode(cs2, rs1, cd, RISCV_SH3ADD) if extensionEnabled(Ext_Zba)
  <-> 0b0010000 @ cs2 @ rs1 @ 0b110 @ cd @ 0b0110011                          if extensionEnabled(Ext_Zba)

mapping clause assembly = ZBA_RTYPE(cs2, rs1, cd, op)
  <-> zba_rtype_mnemonic(op) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: sh123add_32bit capmode
 * Shift by _n_ and add for address generation (SH1ADD, SH2ADD, SH3ADD)
 *
 * sh[1|2|3]add cd, rs1, cs2
 *
 * Increment the address field of cs2 by rs1 shifted left by _n_ bit
 * positions and write the result to cd. The tag bit of the output
 * capability is 0 if cs2 did not have its tag set to 1, the incremented
 * address is outside cs2 's Representable Range or cs2 is sealed.
 */
function clause execute (ZBA_RTYPE_capmode(cs2, rs1, cd, op)) = {
  let rs1_val = X(rs1);
  let cs2_val = C(cs2);
  let shamt : range(0,3) = match op {
    RISCV_SH1ADD => 1,
    RISCV_SH2ADD => 2,
    RISCV_SH3ADD => 3,
  };
  let result = incCapAddrChecked(cs2_val, rs1_val << shamt);
  C(cd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_SH4ADD : (regidx, regidx, regidx)
union clause ast = ZBA_SH4ADD_capmode : (regidx, regidx, regidx)

mapping clause encdec = ZBA_SH4ADD(rs2, rs1, rd)                 if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011             if extensionEnabled(Ext_Zba) & xlen == 64
mapping clause encdec_capmode = ZBA_SH4ADD_capmode(cs2, rs1, cd) if extensionEnabled(Ext_Zba) & xlen == 64
  <-> 0b0010000 @ cs2 @ rs1 @ 0b111 @ cd @ 0b0110011             if extensionEnabled(Ext_Zba) & xlen == 64

mapping clause assembly = ZBA_SH4ADD(rs2, rs1, rd)
  <-> "sh4add" ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = ZBA_SH4ADD_capmode(cs2, rs1, cd)
  <-> "sh4add" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1) ^ sep() ^ cap_reg_name(cs2)

/*!
 * insnref: sh4add_32bit intmode
 * Shift by 4 and add for address generation (SH4ADD)
 *
 * sh4add rd, rs1, rs2
 *
 * Increment rs2 by rs1 shifted left by 4 bit positions and write the
 * result to rd.
 */
function clause execute (ZBA_SH4ADD(rs2, rs1, rd)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let shamt = 4;
  let result = (rs1_val << shamt) + rs2_val;
  X(rd) = result;
  RETIRE_SUCCESS
}

/*!
 * insnref: sh4add_32bit capmode
 * Shift by 4 and add for address generation (SH4ADD)
 *
 * sh4add cd, rs1, cs2
 *
 * Increment the address field of cs2 by rs1 shifted left by 4 bit
 * positions and write the result to cd. The tag bit of the output
 * capability is 0 if cs2 did not have its tag set to 1, the incremented
 * address is outside cs2 's Representable Range or cs2 is sealed.
 */
function clause execute (ZBA_SH4ADD_capmode(cs2, rs1, cd)) = {
  let rs1_val = X(rs1);
  let cs2_val = C(cs2);
  let shamt = 4;
  let result = incCapAddrChecked(cs2_val, rs1_val << shamt);
  C(cd) = result;
  RETIRE_SUCCESS
}
