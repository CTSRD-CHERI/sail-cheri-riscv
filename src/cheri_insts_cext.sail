/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Compressed capability loads/stores (encodings differ between RV32/RV64) */
union clause ast = C_LC : (cregidx, cregidx, bits(9))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FLW], RV64 uses [C.FLD].
mapping clause encdec_compressed_capmode = C_LC(cdc, csc1, ui8 @ ui76 @ ui54 @ 0b0000)                if xlen == 64
  <-> 0b001 @ ui54 : bits(2) @ ui8 : bits(1) @ csc1 : cregidx @ ui76 : bits(2) @ cdc : cregidx @ 0b00 if xlen == 64
mapping clause encdec_compressed_capmode = C_LC(cdc, csc1, 0b0 @ ui76 @ ui53 @ 0b000) if xlen == 32
  <-> 0b011 @ ui53 : bits(3) @ csc1 : cregidx @ ui76 : bits(2) @ cdc : cregidx @ 0b00 if xlen == 32
mapping clause assembly = C_LC(cdc, csc1, uimm)
  <-> "c.lc" ^ spc() ^ cap_creg_name(cdc) ^ sep() ^ cap_creg_name(csc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * insnref: load_16bit_cap_sprel capmode
 * Capability loads (C.LC, C.LCSP), 16-bit encodings
 *
 * c.lc cd', offset(cs1')
 * c.lc cd', offset(csp)
 *
 * Expansion:
 * lc cd', offset(cs1')
 * lc cd', offset(csp)
 *
 * Load capability instruction, authorised by the capability in cs1. Take
 * a load address misaligned exception if not naturally aligned.
 */
function clause execute(C_LC(cdc, csc1, uimm)) = {
  let cd = creg2reg_idx(cdc) in
  let cs1 = creg2reg_idx(csc1) in
  execute(LoadCapImm(cd, cs1, zero_extend(uimm)))
}

union clause ast = C_LCSP : (regidx, bits(10))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FLWSP], RV64 uses [C.FLDSP].
// The encoding with `cd == 0` is reserved and will raise an illegal instruction trap.
mapping clause encdec_compressed_capmode = C_LCSP(cd, ui96 @ ui5 @ ui4 @ 0b0000)  if xlen == 64 & cd != zeros()
  <-> 0b001 @ ui5 : bits(1) @ cd : regidx @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10 if xlen == 64 & cd != zeros()
mapping clause encdec_compressed_capmode = C_LCSP(cd, 0b0 @ ui86 @ ui5 @ ui43 @ 0b000) if xlen == 32 & cd != zeros()
  <-> 0b011 @ ui5 : bits(1) @ cd : regidx @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10     if xlen == 32 & cd != zeros()
mapping clause assembly = C_LCSP(cd, uimm)
  <-> "c.lcsp" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_10(uimm)

/*!
 * insnref: load_16bit_cap_sprel capmode
 * Capability loads (C.LC, C.LCSP), 16-bit encodings
 *
 * c.lc cd', offset(cs1')
 * c.lc cd', offset(csp)
 *
 * Expansion:
 * lc cd', offset(cs1')
 * lc cd', offset(csp)
 *
 * Load capability instruction, authorised by the capability in cs1. Take
 * a load address misaligned exception if not naturally aligned.
 */
function clause execute(C_LCSP(cd, uimm)) =
  execute(LoadCapImm(cd, sp, zero_extend(uimm)))

/*
 * The c.lcsp encoding with cd == 0 should raise an illegal instruction trap
 * instead of falling back to the non-capmode (legal) instruction
 * `c.flwsp/fldsp f0` so we need an explicit capmode illegal match clause.
 */
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b001 @ ui5 @ 0b00000 @ ui4 @ ui96 @ 0b10) if xlen == 64
  <-> 0b001 @ ui5 : bits(1) @ 0b00000 @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10                   if xlen == 64
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b011 @ ui5 @ 0b00000 @ ui43 @ ui86 @ 0b10) if xlen == 32
  <-> 0b011 @ ui5 : bits(1) @ 0b00000 @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10                   if xlen == 32

union clause ast = C_SC : (cregidx, cregidx, bits(9))

// This instruction is only available in capability encoding mode.
// For RV32 this replaces the encoding of [C.FSW], RV64 uses [C.FSD].
mapping clause encdec_compressed_capmode = C_SC(csc2, csc1, ui8 @ ui76 @ ui54 @ 0b0000)                if xlen == 64
  <-> 0b101 @ ui54 : bits(2) @ ui8 : bits(1) @ csc1 : bits(3) @ ui76 : bits(2) @ csc2 : bits(3) @ 0b00 if xlen == 64
mapping clause encdec_compressed_capmode = C_SC(csc2, csc1, 0b0 @ ui76 @ ui53 @ 0b000) if xlen == 32
  <-> 0b111 @ ui53 : bits(3) @ csc1 : bits(3) @ ui76 : bits(2) @ csc2 : bits(3) @ 0b00 if xlen == 32
mapping clause assembly = C_SC(csc2, csc1, uimm)
  <-> "c.sc" ^ spc() ^ cap_creg_name(csc2) ^ sep() ^ cap_creg_name(csc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * insnref: store_16bit_cap_sprel capmode
 * Stores (C.SC, C.SCSP), 16-bit encodings
 *
 * c.sc cs2', offset(cs1')
 * c.sc cs2', offset(csp)
 *
 * Expansion:
 * sc cs2', offset(cs1')
 * sc cs2', offset(csp)
 *
 * Store capability instruction, authorised by the capability in cs1.
 * Take a store/AMO address misaligned exception if not naturally
 * aligned.
 */
function clause execute(C_SC(csc2, csc1, uimm)) = {
  let cs2 = creg2reg_idx(csc2) in
  let cs1 = creg2reg_idx(csc1) in
  execute(StoreCapImm(cs2, cs1, zero_extend(uimm)))
}

union clause ast = C_SCSP : (regidx, bits(10))

// This instruction is only available in capability encoding mode.
/// For RV32 this replaces the encoding of [C.FSWSP], RV64 uses [C.FSDSP].
mapping clause encdec_compressed_capmode = C_SCSP(cs2, ui96 @ ui54 @ 0b0000) if xlen == 64
  <-> 0b101 @ ui54 : bits(2) @ ui96 : bits(4) @ cs2 : regidx @ 0b10          if xlen == 64
mapping clause encdec_compressed_capmode = C_SCSP(cs2, 0b0 @ ui86 @ ui53 @ 0b000) if xlen == 32
  <-> 0b111 @ ui53 : bits(3) @ ui86 : bits(3) @ cs2 : regidx @ 0b10               if xlen == 32
mapping clause assembly = C_SCSP(cs2, uimm)
  <-> "c.scsp" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_10(uimm)

/*!
 * insnref: store_16bit_cap_sprel capmode
 * Stores (C.SC, C.SCSP), 16-bit encodings
 *
 * c.sc cs2', offset(cs1')
 * c.sc cs2', offset(csp)
 *
 * Expansion:
 * sc cs2', offset(cs1')
 * sc cs2', offset(csp)
 *
 * Store capability instruction, authorised by the capability in cs1.
 * Take a store/AMO address misaligned exception if not naturally
 * aligned.
 */
function clause execute(C_SCSP(cs2, uimm)) =
  execute(StoreCapImm(cs2, sp, zero_extend(uimm)))

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
 * cadd csp, csp, imm
 *
 * Add the non-zero sign-extended 6-bit immediate to the value in the
 * stack pointer (csp=c2), where the immediate is scaled to represent
 * multiples of 16 in the range (-512,496). Clear the tag if the
 * resulting capability is unrepresentable or csp is sealed.
 */
function clause execute(C_ADDI16SP_capmode(nzimm)) =
  execute(CADDI(sp, sp, sign_extend(nzimm)))

union clause ast = C_ADDI4SPN_capmode : (cregidx, bits(10))

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.ADDI4SPN].
mapping clause encdec_compressed_capmode = C_ADDI4SPN_capmode(cdc, nz96 @ nz54 @ nz3 @ nz2 @ 0b00)
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
  <-> 0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ cdc : cregidx @ 0b00
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
mapping clause assembly = C_ADDI4SPN_capmode(cdc, nzuimm)                     if nzuimm != 0b0000000000
  <-> "c.addi4spn" ^ spc() ^ cap_creg_name(cdc) ^ sep() ^ hex_bits_10(nzuimm) if nzuimm != 0b0000000000

/*!
 * insnref: addi4spn_16bit capmode
 * Stack pointer increment in blocks of 4 (C.ADDI4SPN), 16-bit encoding
 *
 * c.addi4spn cd', uimm
 *
 * Expansion:
 * cadd cd', csp, uimm
 *
 * Add a zero-extended non-zero immediate, scaled by 4, to the stack
 * pointer, csp, and writes the result to cd'. This instruction is used
 * to generate pointers to stack-allocated variables. Clear the tag if
 * the resulting capability is unrepresentable or csp is sealed.
 */
function clause execute(C_ADDI4SPN_capmode(cdc, nzuimm)) = {
  let cd = creg2reg_idx(cdc) in
  execute(CADDI(cd, sp, zero_extend(nzuimm)))
}

/* Control flow */
union clause ast = C_JALR_capmode : (regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.JALR].
mapping clause encdec_compressed_capmode = C_JALR_capmode(cs1) if cs1 != zreg
  <-> 0b100 @ 0b1 @ cs1 : regidx @ 0b00000 @ 0b10              if cs1 != zreg
mapping clause assembly = C_JALR_capmode(cs1)              if cs1 != zreg
  <-> "c.jalr" ^ spc() ^ "cra" ^ sep() ^ cap_reg_name(cs1) if cs1 != zreg

/*!
 * insnref: jalr_16bit capmode
 * Jump register with link, 16-bit encodings
 *
 * c.jalr c1, cs1
 *
 * Expansion:
 * jalr c1, 0(cs1)
 *
 * See JALR for execution of the expanded instruction as shown above.
 * Note that the offset is zero in the expansion.
 */
function clause execute(C_JALR_capmode(cs1)) = execute(JALR_capmode(zeros(), cs1, ra))

union clause ast = C_JR_capmode : (regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.JR].
mapping clause encdec_compressed_capmode = C_JR_capmode(cs1) if cs1 != zreg
  <-> 0b100 @ 0b0 @ cs1 : regidx @ 0b00000 @ 0b10            if cs1 != zreg
mapping clause assembly = C_JR_capmode(cs1) if cs1 != zreg
  <-> "c.jr" ^ spc() ^ cap_reg_name(cs1)    if cs1 != zreg

/*!
 * insnref: jr_16bit capmode
 * Jump register without link, 16-bit encodings
 *
 * c.jr cs1
 *
 * Expansion:
 * jalr c0, 0(cs1)
 *
 * See JALR for execution of the expanded instruction as shown above.
 * Note that the offset is zero in the expansion.
 */
function clause execute(C_JR_capmode(cs1)) = execute(JALR_capmode(zeros(), cs1, zreg))

union clause ast = C_JAL_capmode : (bits(12))

// This instruction is only available in capability encoding mode.
// This instruction is only available in RV32.
// This instruction replaces the encoding of [C.JAL].
mapping clause encdec_compressed_capmode = C_JAL_capmode(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31 @ 0b0) if xlen == 32
  <-> 0b001 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01
      if xlen == 32
mapping clause assembly = C_JAL_capmode(imm) if xlen == 32
  <-> "c.jal" ^ spc() ^ "cra" ^ sep() ^ hex_bits_12(imm) if xlen == 32

/*!
 * insnref: jal_16bit capmode
 * Jump with link, 16-bit encodings
 *
 * c.jal c1, offset
 *
 * Link the next linear pcc to cd and seal. Jump to pcc.address+offset.
 */
function clause execute(C_JAL_capmode(imm)) = execute(JAL_capmode(sign_extend(imm), ra))

union clause ast = C_MV_capmode : (regidx, regidx)

// This instruction is only available in capability encoding mode.
// This instruction replaces the encoding of [C.MV].
mapping clause encdec_compressed_capmode = C_MV_capmode(cd, cs2)
  if cd != zreg & cs2 != zreg
    <-> 0b100 @ 0b0 @ cd : regidx @ cs2 : regidx @ 0b10
  if cd != zreg & cs2 != zreg

/*!
 * insnref: cmv_16bit capmode
 * Capability move (C.MV), 16-bit encoding
 *
 * c.mv cd, cs2
 *
 * Expansion:
 * cmv cd, cs2
 *
 * Capability register cd is replaced with the contents of cs2.
 */
function clause execute(C_MV_capmode(cd, cs2)) = execute(CMV(cd, cs2))

mapping clause assembly = C_MV_capmode(cd, cs2)
  if cd != zreg & cs2 != zreg
    <-> "c.mv" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs2)
  if cd != zreg & cs2 != zreg

union clause ast = C_MODESW : unit

// C.MODESW is valid in capability and integer pointer modes.
mapping clause encdec_compressed = C_MODESW()     if cheri_registers_enabled()
  <-> 0b100 @ 0b111 @ 0b000 @ 0b11 @ 0b111 @ 0b01 if cheri_registers_enabled()

mapping clause assembly = C_MODESW() <-> "c.modesw"

/*!
 * insnref: modesw_16bit
 * Capability/_Integer Pointer Mode_ switching (C.MODESW), 16-bit
 * encoding
 *
 * c.modesw
 *
 * Expansion:
 * modesw
 *
 * Toggle the hart's current CHERI execution mode in pcc.
 *
 * * If the current mode in pcc is _Integer Pointer Mode_ (1), then the
 * M-bit in pcc is set to _Capability Pointer Mode_ (0).
 * * If the current mode is _Capability Pointer Mode_ (0), then the M-bit
 * in pcc is set to _Integer Pointer Mode_ (1).
 */
function clause execute(C_MODESW()) = execute(MODESW())
