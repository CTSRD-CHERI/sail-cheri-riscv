/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Compressed capability loads/stores (encodings differ between RV32/RV64) */
union clause ast = C_LY : (cregidx, cregidx, bits(9))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FLW], RV64 uses [C.FLD].
mapping clause encdec_compressed_capmode = C_LY(rdc, rsc1, ui8 @ ui76 @ ui54 @ 0b0000)                              if xlen == 64
  <-> 0b001 @ ui54 : bits(2) @ ui8 : bits(1) @ encdec_creg(rsc1) @ ui76 : bits(2) @ encdec_creg(rdc) @ 0b00 if xlen == 64
mapping clause encdec_compressed_capmode = C_LY(rdc, rsc1, 0b0 @ ui76 @ ui53 @ 0b000)               if xlen == 32
  <-> 0b011 @ ui53 : bits(3) @ encdec_creg(rsc1) @ ui76 : bits(2) @ encdec_creg(rdc) @ 0b00 if xlen == 32
mapping clause assembly = C_LY(rdc, rsc1, uimm)
  <-> "c.ly" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * insnref: load_16bit_cap_sprel capmode
 * Capability loads (C.LY, C.LYSP), 16-bit encodings
 *
 * c.ly rd', offset(rs1')
 * c.ly rd', offset(sp)
 *
 * Expansion:
 * ly rd', offset(rs1')
 * ly rd', offset(sp)
 *
 * Load capability instruction, authorised by the capability in rs1. Take
 * a load address misaligned exception if not naturally aligned.
 */
function clause execute(C_LY(rdc, rsc1, uimm)) = {
  let rd = creg2reg_idx(rdc) in
  let rs1 = creg2reg_idx(rsc1) in
  execute(LoadCapImm(rd, rs1, zero_extend(uimm)))
}

union clause ast = C_LYSP : (regidx, bits(10))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FLWSP], RV64 uses [C.FLDSP].
// The encoding with `rd == 0` is reserved and will raise an illegal instruction trap.
mapping clause encdec_compressed_capmode = C_LYSP(rd, ui96 @ ui5 @ ui4 @ 0b0000)     if xlen == 64 & rd != zreg
  <-> 0b001 @ ui5 : bits(1) @ encdec_reg(rd) @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10 if xlen == 64 & rd != zreg
mapping clause encdec_compressed_capmode = C_LYSP(rd, 0b0 @ ui86 @ ui5 @ ui43 @ 0b000) if xlen == 32 & rd != zreg
  <-> 0b011 @ ui5 : bits(1) @ encdec_reg(rd) @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10  if xlen == 32 & rd != zreg
mapping clause assembly = C_LYSP(rd, uimm)
  <-> "c.lysp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_10(uimm)

/*!
 * insnref: load_16bit_cap_sprel capmode
 * Capability loads (C.LY, C.LYSP), 16-bit encodings
 *
 * c.ly rd', offset(rs1')
 * c.ly rd', offset(sp)
 *
 * Expansion:
 * ly rd', offset(rs1')
 * ly rd', offset(sp)
 *
 * Load capability instruction, authorised by the capability in rs1. Take
 * a load address misaligned exception if not naturally aligned.
 */
function clause execute(C_LYSP(rd, uimm)) =
  execute(LoadCapImm(rd, sp, zero_extend(uimm)))

/*
 * The c.lysp encoding with rd == 0 should raise an illegal instruction trap
 * instead of falling back to the non-capmode (legal) instruction
 * `c.flwsp/fldsp f0` so we need an explicit capmode illegal match clause.
 */
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b001 @ ui5 @ 0b00000 @ ui4 @ ui96 @ 0b10) if xlen == 64
  <-> 0b001 @ ui5 : bits(1) @ 0b00000 @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10                   if xlen == 64
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b011 @ ui5 @ 0b00000 @ ui43 @ ui86 @ 0b10) if xlen == 32
  <-> 0b011 @ ui5 : bits(1) @ 0b00000 @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10                   if xlen == 32

union clause ast = C_SY : (cregidx, cregidx, bits(9))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FSW], RV64 uses [C.FSD].
mapping clause encdec_compressed_capmode = C_SY(rsc2, rsc1, ui8 @ ui76 @ ui54 @ 0b0000)                      if xlen == 64
  <-> 0b101 @ ui54 : bits(2) @ ui8 : bits(1) @ encdec_creg(rsc1) @ ui76 : bits(2) @ encdec_creg(rsc2) @ 0b00 if xlen == 64
mapping clause encdec_compressed_capmode = C_SY(rsc2, rsc1, 0b0 @ ui76 @ ui53 @ 0b000)       if xlen == 32
  <-> 0b111 @ ui53 : bits(3) @ encdec_creg(rsc1) @ ui76 : bits(2) @ encdec_creg(rsc2) @ 0b00 if xlen == 32
mapping clause assembly = C_SY(rsc2, rsc1, uimm)
  <-> "c.sy" ^ spc() ^ creg_name(rsc2) ^ sep() ^ creg_name(rsc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * insnref: store_16bit_cap_sprel capmode
 * Stores (C.SY, C.SYSP), 16-bit encodings
 *
 * c.sy rs2', offset(rs1')
 * c.sy rs2', offset(sp)
 *
 * Expansion:
 * sy rs2', offset(rs1')
 * sy rs2', offset(sp)
 *
 * Store capability instruction, authorised by the capability in rs1.
 * Take a store/AMO address misaligned exception if not naturally
 * aligned.
 */
function clause execute(C_SY(rsc2, rsc1, uimm)) = {
  let rs2 = creg2reg_idx(rsc2) in
  let rs1 = creg2reg_idx(rsc1) in
  execute(StoreCapImm(rs2, rs1, zero_extend(uimm)))
}

union clause ast = C_SYSP : (regidx, bits(10))

// This instruction is only available in capability encoding mode.
/// For RV32 this replaces the encoding of [C.FSWSP], RV64 uses [C.FSDSP].
mapping clause encdec_compressed_capmode = C_SYSP(rs2, ui96 @ ui54 @ 0b0000) if xlen == 64
  <-> 0b101 @ ui54 : bits(2) @ ui96 : bits(4) @ encdec_reg(rs2) @ 0b10       if xlen == 64
mapping clause encdec_compressed_capmode = C_SYSP(rs2, 0b0 @ ui86 @ ui53 @ 0b000) if xlen == 32
  <-> 0b111 @ ui53 : bits(3) @ ui86 : bits(3) @ encdec_reg(rs2) @ 0b10            if xlen == 32
mapping clause assembly = C_SYSP(rs2, uimm)
  <-> "c.sysp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_10(uimm)

/*!
 * insnref: store_16bit_cap_sprel capmode
 * Stores (C.SY, C.SYSP), 16-bit encodings
 *
 * c.sy rs2', offset(rs1')
 * c.sy rs2', offset(sp)
 *
 * Store capability instruction, authorised by the capability in rs1.
 * Take a store/AMO address misaligned exception if not naturally
 * aligned.
 */
function clause execute(C_SYSP(rs2, uimm)) =
  execute(StoreCapImm(rs2, sp, zero_extend(uimm)))

/* Capability arithmetic instructions */
union clause ast = C_ADDI16SP_capmode : (bits(10))

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.ADDI16SP].
mapping clause encdec_compressed_capmode = C_ADDI16SP_capmode(nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 @ 0b0000)
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
  <-> 0b011 @ nzi9 : bits(1) @ /* x2 */ 0b00010 @ nzi4 : bits(1) @ nzi6 : bits(1) @ nzi87 : bits(2) @ nzi5 : bits(1) @ 0b01
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
mapping clause assembly = C_ADDI16SP_capmode(nzimm) if nzimm != 0b0000000000
  <-> "c.addi16sp" ^ spc() ^ hex_bits_10(nzimm)     if nzimm != 0b0000000000

/*!
 * insnref: addi16sp_16bit capmode
 * Stack pointer increment in blocks of 16 (C.ADDI16SP), 16-bit encodings
 *
 * c.addi16sp imm
 *
 * Expansion:
 * addy sp, sp, imm
 *
 * Add the non-zero sign-extended 6-bit immediate to the value in the
 * stack pointer (sp=x2), where the immediate is scaled to represent
 * multiples of 16 in the range (-512,496). Clear the tag if the
 * resulting capability is unrepresentable or sp is sealed.
 */
function clause execute(C_ADDI16SP_capmode(nzimm)) =
  execute(ADDIY(sp, sp, sign_extend(nzimm)))

union clause ast = C_ADDI4SPN_capmode : (cregidx, bits(10))

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.ADDI4SPN].
mapping clause encdec_compressed_capmode = C_ADDI4SPN_capmode(rdc, nz96 @ nz54 @ nz3 @ nz2 @ 0b00)
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
  <-> 0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ encdec_creg(rdc) @ 0b00
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
mapping clause assembly = C_ADDI4SPN_capmode(rdc, nzuimm)                     if nzuimm != 0b0000000000
  <-> "c.addi4spn" ^ spc() ^ creg_name(rdc) ^ sep() ^ hex_bits_10(nzuimm) if nzuimm != 0b0000000000

/*!
 * insnref: addi4spn_16bit capmode
 * Stack pointer increment in blocks of 4 (C.ADDI4SPN), 16-bit encoding
 *
 * c.addi4spn rd', uimm
 *
 * Expansion:
 * addy rd', sp, uimm
 *
 * Add a zero-extended non-zero immediate, scaled by 4, to the stack
 * pointer, sp, and writes the result to rd'. This instruction is used
 * to generate pointers to stack-allocated variables. Clear the tag if
 * the resulting capability is unrepresentable or sp is sealed.
 */
function clause execute(C_ADDI4SPN_capmode(rdc, nzuimm)) = {
  let rd = creg2reg_idx(rdc) in
  execute(ADDIY(rd, sp, zero_extend(nzuimm)))
}

/* Control flow */
union clause ast = C_JALR_capmode : (regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.JALR].
mapping clause encdec_compressed_capmode = C_JALR_capmode(rs1) if rs1 != zreg
  <-> 0b100 @ 0b1 @ encdec_reg(rs1) @ 0b00000 @ 0b10           if rs1 != zreg
mapping clause assembly = C_JALR_capmode(rs1)              if rs1 != zreg
  <-> "c.jalr" ^ spc() ^ "ra" ^ sep() ^ reg_name(rs1) if rs1 != zreg

/*!
 * insnref: jalr_16bit capmode
 * Jump register with link, 16-bit encodings
 *
 * c.jalr ra, rs1
 *
 * Expansion:
 * jalr ra, 0(rs1)
 *
 * See JALR for execution of the expanded instruction as shown above.
 * Note that the offset is zero in the expansion.
 */
function clause execute(C_JALR_capmode(rs1)) = execute(JALR_capmode(zeros(), rs1, ra))

union clause ast = C_JR_capmode : (regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.JR].
mapping clause encdec_compressed_capmode = C_JR_capmode(rs1) if rs1 != zreg
  <-> 0b100 @ 0b0 @ encdec_reg(rs1) @ 0b00000 @ 0b10         if rs1 != zreg
mapping clause assembly = C_JR_capmode(rs1) if rs1 != zreg
  <-> "c.jr" ^ spc() ^ reg_name(rs1)    if rs1 != zreg

/*!
 * insnref: jr_16bit capmode
 * Jump register without link, 16-bit encodings
 *
 * c.jr rs1
 *
 * Expansion:
 * jalr zero, 0(rs1)
 *
 * See JALR for execution of the expanded instruction as shown above.
 * Note that the offset is zero in the expansion.
 */
function clause execute(C_JR_capmode(rs1)) = execute(JALR_capmode(zeros(), rs1, zreg))

union clause ast = C_JAL_capmode : (bits(12))

// This instruction is only available in capability encoding mode.
// This instruction is only available in RV32.
// This instruction replaces the encoding of [C.JAL].
mapping clause encdec_compressed_capmode = C_JAL_capmode(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31 @ 0b0) if xlen == 32
  <-> 0b001 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01
      if xlen == 32
mapping clause assembly = C_JAL_capmode(imm) if xlen == 32
  <-> "c.jal" ^ spc() ^ "ra" ^ sep() ^ hex_bits_12(imm) if xlen == 32

/*!
 * insnref: jal_16bit capmode
 * Jump with link, 16-bit encodings
 *
 * c.jal ra, offset
 *
 * Link the next linear pcc to rd and seal. Jump to pcc.address+offset.
 */
function clause execute(C_JAL_capmode(imm)) = execute(JAL_capmode(sign_extend(imm), ra))

union clause ast = C_YMV : (regidx, regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.MV].
mapping clause encdec_compressed_capmode = C_YMV(rd, rs2)
  if rd != zreg & rs2 != zreg
    <-> 0b100 @ 0b0 @ encdec_reg(rd) @ encdec_reg(rs2) @ 0b10
  if rd != zreg & rs2 != zreg

/*!
 * insnref: ymv_16bit capmode
 * Capability move (C.MV), 16-bit encoding
 *
 * c.ymv rd, rs2
 *
 * Expansion:
 * ymv rd, rs2
 *
 * Capability register rd is replaced with the contents of rs2.
 */
function clause execute(C_YMV(rd, rs2)) = execute(YMV(rd, rs2))

mapping clause assembly = C_YMV(rd, rs2)
  if rd != zreg & rs2 != zreg
    <-> "c.ymv" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2)
  if rd != zreg & rs2 != zreg
