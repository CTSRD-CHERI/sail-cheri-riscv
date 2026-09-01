/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Capability versions of mode-dependent instructions */

union clause ast = AUIPC_capmode : (bits(20), regidx)
/*!
 * insnref: auipc_32bit capmode
 * Add upper immediate to *pc* /pcc
 *
 * auipc rd, imm
 *
 * Form a 32-bit offset from the 20-bit immediate filling the lowest 12
 * bits with zeros. Increment the address of the AUIPC instruction's pcc
 * by the 32-bit offset, then write the output capability to rd. The tag
 * bit of the output capability is 0 if the incremented address is
 * outside the pcc's Representable Range.
 */
function clause execute AUIPC_capmode(imm, rd) = {
  let off : xlenbits = sign_extend(imm @ 0x000);
  let (representable, newCap) = setCapAddr(PCC, PC + off);
  Y(rd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}

union clause ast = JAL_capmode : (bits(21), regidx)
/*!
 * insnref: jal_32bit capmode
 * Jump and link
 *
 * jal rd, offset
 *
 * JAL's immediate encodes a signed offset in multiple of 2 bytes. The
 * pcc is incremented by the sign-extended offset to form the jump target
 * capability. The target capability is written to pcc. The pcc of the
 * next instruction following the jump is sealed and written to rd.
 */
function clause execute(JAL_capmode(imm, rd)) = {
  let off : xlenbits = sign_extend(imm);
  let newPC = PC + off;
  if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(virtaddr(newPC), E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    Y(rd) = sealCap(linkCap);
    set_next_pc(newPC);
    RETIRE_SUCCESS
  }
}

union clause ast = JALR_capmode : (bits(12), regidx, regidx)
/*!
 * insnref: jalr_32bit capmode
 * Jump and link register
 *
 * jalr rd, rs1, offset
 *
 * JALR allows unconditional, indirect jumps to a target capability. The
 * target capability is unsealed if the offset is zero. The target
 * address is obtained by adding the sign-extended 12-bit offset to
 * rs1.address, then setting the least-significant bit of the result to
 * zero. The target capability may have Invalid address conversion
 * performed and is then installed in pcc. The pcc of the next
 * instruction following the jump is sealed and written to rd.
 */
function clause execute(JALR_capmode(imm, rs1, rd)) = {
  let rs1_cap = Y(rs1);

  // Calculate new PC which may be offset from the capability address.
  let off : xlenbits = sign_extend(imm);
  let newPC = [rs1_cap.address + off with 0 = bitzero]; /* clear bit zero as for RISCV JALR */

  if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(virtaddr(newPC), E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    Y(rd) = sealCap(linkCap);
    set_next_pc(newPC);

    // Construct the new capability pointing to the address + offset.
    let (representable, newPCC) = setCapAddr(rs1_cap, newPC);
    set_next_pcc(clearTagIf(unsealCap(newPCC), not(representable)));

    RETIRE_SUCCESS
  }
}

union clause ast = BEQ_reserved_capmode : (bits(13), regidx, regidx)
function clause execute(BEQ_reserved_capmode(_, _, _)) = {
  handle_illegal();
  RETIRE_FAIL
}

union clause ast = BNE_reserved_capmode : (bits(13), regidx, regidx)
function clause execute(BNE_reserved_capmode(_, _, _)) = {
  handle_illegal();
  RETIRE_FAIL
}

/* Operations that extract parts of a capability into GPR */

union clause ast = YPERMR : (regidx, regidx)
union clause ast = YBASER : (regidx, regidx)
union clause ast = YTOPR  : (regidx, regidx)
union clause ast = YLENR  : (regidx, regidx)
union clause ast = YTAGR  : (regidx, regidx)
union clause ast = YMODER : (regidx, regidx)
union clause ast = YTYPER : (regidx, regidx)

union clause ast = SRLIY  : (regidx, regidx)

/*!
 * insnref: ymoder_32bit brief
 * Capability get CHERI execution mode
 *
 * ymoder rd, rs1
 *
 * See ISA document for full description
 */
function clause execute (YMODER(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = zero_extend(pointer_mode_encdec(getCapMode(rs1_cap)));
  RETIRE_SUCCESS
}

/*!
 * insnref: ytyper_32bit brief
 * Capability get type
 *
 * ytyper rd, rs1
 *
 * See ISA document for full description
 */
function clause execute (YTYPER(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = zero_extend(bool_to_bits(rs1_cap.sealed));
  RETIRE_SUCCESS
}

/*!
 * insnref: ypermr_32bit brief
 * Capability get permissions
 *
 * ypermr rd, rs1
 *
 * See ISA document for full description
 */
function clause execute (YPERMR(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = packPerms(getArchPermsLegalized(rs1_cap), rs1_cap.gl, rs1_cap.sd_perms).bits;
  RETIRE_SUCCESS
}

/*!
 * insnref: ybaser_32bit
 * Capability get base address
 *
 * ybaser rd, rs1
 *
 * Decode the base integer address from rs1's bounds and write the result
 * to rd. It is not required that the input capability rs1  has its tag
 * set to 1.
 */

function clause execute (YBASER(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = match getCapBoundsBits(rs1_cap) {
    None() => zeros(),
    Some(base, _) => base
  };
  RETIRE_SUCCESS
}

/*!
 * insnref: ytopr_32bit
 * Capability get top address
 *
 * ytopr rd, rs1
 *
 * Decode the top integer address from rs1's bounds and write the result
 * to rd, saturated to XLEN bits. It is not required that the input
 * capability rs1  has its tag set to 1.
 */

function clause execute (YTOPR(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  let top : CapLenInt = match getCapBounds(rs1_cap) {
    None() => 0,
    Some(_, top) => top
  };
  X(rd) = to_bits(xlen, if top > cap_max_addr then cap_max_addr else top) ;
  RETIRE_SUCCESS
}

/*!
 * insnref: srliy_32bit
 * Capability get metadata
 *
 * srliy rd, rs1
 *
 * Copy the metadata (bits [YLEN-1:XLEN]) of capability rs1 into rd.
 */
function clause execute (SRLIY(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = capToMetadataBits(rs1_cap).bits;
  RETIRE_SUCCESS
}

union clause ast = PACKY : (regidx, regidx, regidx)
/*!
 * insnref: packy_32bit
 * Capability set metadata
 *
 * packy rd, rs1, rs2
 *
 * Packs the least-significant XLEN-bits of rs1 and rs2 into
 * rd, and set rd.tag=0.
 */
function clause execute (PACKY(rd, rs1, rs2)) = {
  let lo = X(rs1);
  let hi = X(rs2);
  let newCap = bitsToCap(false, hi @ lo);
  Y(rd) = newCap;
  RETIRE_SUCCESS
}

/*!
 * insnref: ylenr_32bit
 * Capability get length
 *
 * ylenr rd, rs1
 *
 * Calculate the length of rs1's bounds and write the result in rd. The
 * length is defined as the difference between the decoded bounds' top
 * and base addresses i.e. top - base. It is not required that the input
 * capability rs1  has its tag set to 1. YLENR outputs 0 if rs1's bounds
 * are malformed (see Malformed Capability Bounds), and 2^XLEN^-1 if the
 * length of rs1 is 2^XLEN^.
 */
function clause execute (YLENR(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  // getCapLength returns 0 if the bounds are malformed
  let len = getCapLength(rs1_cap);
  X(rd) = to_bits(xlen, if len > cap_max_addr then cap_max_addr else len);
  RETIRE_SUCCESS
}

/*!
 * insnref: ytagr_32bit
 * Capability get tag
 *
 * ytagr rd, rs1
 *
 * Zero extend the value of rs1.tag and write the result to rd.
 */
function clause execute (YTAGR(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  X(rd) = zero_extend(bool_to_bits(rs1_cap.tag));
  RETIRE_SUCCESS
}

union clause ast = YPERMC : (regidx, regidx, regidx)
/*!
 * insnref: ypermc_32bit brief
 * Mask capability permissions
 *
 * ypermc rd, rs1, rs2
 *
 * See ISA document for full description
 */
function clause execute(YPERMC(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_val = X(rs2);

  let cond = capIsSealed(rs1_cap) | capIsMalformed(rs1_cap);
  let inCap = clearTagIf(rs1_cap, cond);

  let old_perms = packPerms(getArchPermsLegalized(inCap), inCap.gl, inCap.sd_perms).bits;

  let new_perms = old_perms & ~(rs2_val);

  let (new_arch_perms, new_gl, new_sd_perms) = unpackPerms(struct {bits = new_perms});
  let newCap = { setArchPerms(inCap, new_arch_perms) with gl = new_gl, sd_perms = new_sd_perms };

  Y(rd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YMODEW : (regidx, regidx, regidx)
/*!
 * insnref: ymodew_32bit
 * Capability set CHERI execution mode
 *
 * ymodew rd, rs1, rs2
 *
 * Copy rs1 to rd. Clear rd.tag if rs1 is sealed. Update the P-bit of rd
 * to the least significant bit of rs2 if the two following conditions
 * are met, otherwise do not update it:
 * . X-permission is set
 * . The existing permissions can be produced by YPERMC
 */
function clause execute(YMODEW(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let mode = pointer_mode_encdec(X(rs2)[0 .. 0]);

  let cond = capIsSealed(rs1_cap) | capIsMalformed(rs1_cap);
  let rs1_cap = clearTagIf(rs1_cap, cond);

  let hasMode = canX(rs1_cap);
  let newCap = if hasMode & not(cond) then setCapMode(rs1_cap, mode) else rs1_cap;

  Y(rd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YMODESW : (PointerMode)
/*!
 * insnref: ymodesw_32bit
 * Switch CHERI execution mode
 *
 * ymodeswy
 * ymodeswi
 *
 * Set the hart's current CHERI execution mode in <<pcc>>.
 *
 * * YMODESWY: If the current mode in pcc is _Integer Pointer Mode_ (1), then the
 *   P-bit in pcc is set to _Capability Pointer Mode_ (0). Otherwise no effect.
 * * YMODESWI: If the current mode in pcc is _Capability Pointer Mode_ (0), then the P-bit
 *   in pcc is set to _Integer Pointer Mode_ (1). Otherwise no effect.
 *
 * Executing YMODESWY or YMODESWI from the program buffer in debug mode updates
 * the P-bit of drootc. The P-bit of drootc sets the CHERI execution mode for the execution
 * of the next instruction from the program buffer, and is used to control which CHERI
 * execution mode to enter next time debug mode is entered. The CHERI execution mode
 * is only controlled by the P-bit of drootc in debug mode.
 */
function clause execute(YMODESW(mode)) = {
  if getCapMode(PCC) != mode then {
    set_next_pcc(setCapMode(PCC, mode));
  };
  // if debug_mode_active then drootc = setCapMode(root_cap, mode);
  RETIRE_SUCCESS
}

union clause ast = YADD : (regidx, regidx, regidx)
/*!
 * insnref: yadd_32bit
 * Capability pointer increment
 *
 * yadd rd, rs1, rs2
 * yaddi rd, rs1, imm
 *
 * Increment the address field of the capability rs1  and write the
 * result to rd . The tag bit of the output capability is 0 if rs1  did
 * not have its tag set to 1, the incremented address is outside rs1's
 * Representable Range or rs1  is sealed.
 *
 * For YADD, the address is incremented by the value in rs2 .
 * For YADDI, the address is incremented by the immediate value imm.
 */
function clause execute (YADD(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_val = X(rs2);

  let newCap = incCapAddrChecked(rs1_cap, rs2_val);

  Y(rd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YADDI : (regidx, regidx, bits(12))
/*!
 * insnref: yadd_32bit
 * Capability pointer increment
 *
 * yadd rd, rs1, rs2
 * yaddi rd, rs1, imm
 *
 * Increment the address field of the capability rs1  and write the
 * result to rd . The tag bit of the output capability is 0 if rs1  did
 * not have its tag set to 1, the incremented address is outside rs1's
 * Representable Range or rs1  is sealed.
 *
 * For YADD, the address is incremented by the value in rs2 .
 * For YADDI, the address is incremented by the immediate value imm.
 */
function clause execute (YADDI(rd, rs1, imm)) = {
  let rs1_cap = Y(rs1);
  let immBits : xlenbits = sign_extend(imm);

  let newCap = incCapAddrChecked(rs1_cap, immBits);

  Y(rd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YADDRW : (regidx, regidx, regidx)
/*!
 * insnref: yaddrw_32bit
 * Capability set address
 *
 * yaddrw rd, rs1, rs2
 *
 * Set the address field of capability rs1 to rs2 and write the output
 * capability to rd. The tag bit of the output capability is 0 if rs1 did
 * not have its tag set to 1, rs2 is outside the Representable Range of
 * rs1 or if rs1 is sealed.
 */
function clause execute (YADDRW(rd, rs1, rs2)) = {
  Y(rd) = setCapAddrChecked(Y(rs1), X(rs2));
  RETIRE_SUCCESS
}

union clause ast = YBNDSRW : (regidx, regidx, regidx)
/*!
 * insnref: ybndsrw_32bit
 * Capability set bounds, rounding up if necessary
 *
 * ybndsrw rd, rs1, rs2
 *
 * Capability register rd  is set to capability register rs1  with the
 * base address of its bounds replaced with the value of rs1.address
 * field and the length of its bounds set to rs2. The base is rounded
 * down and the length is rounded up by the smallest amount needed to
 * form a representable capability covering the requested bounds. In all
 * cases, rd.tag is set to 0 if its bounds exceed rs1's bounds, rs1's tag
 * is 0 or rs1  is sealed.
 */
function clause execute (YBNDSRW(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let length = X(rs2);
  let newBase = rs1_cap.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(rs1_cap, newBase, unsigned(length));
  let (_, newCap) : (bool, Capability) = setCapBounds(rs1_cap, newBase, newTop);
  let cond = not(inBounds) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(rd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YBNDSWI : (regidx, regidx, bits(9))

mapping encdec_ybndsw_imm : bits(9) <-> bits(13) = {
  0b0_0000_0000                                <-> 0b1_0000_0000_0000,
  0b0 @ i7_0                  if i7_0 != 0x00  <-> 0b0_0000 @ i7_0              if i7_0 != 0x00,
  0b1_000 @ i4 @ i3_0:bits(4)                  <-> 0b0_0001 @ i3_0 @ i4 @ 0b000,
  0b1 @ i7_5 @ i4_0:bits(5)   if i7_5 != 0b000 <-> 0b0 @ i7_5 @ i4_0 @ 0b0000   if i7_5 != 0b000,
}
/*!
 * insnref: ybndsw_32bit
 * Capability set bounds
 *
 * ybndsw rd, rs1, rs2
 * ybndswi rd, rs1, uimm
 *
 * Capability register rd  is set to capability register rs1  with the
 * base address of its bounds replaced with the value of rs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set rd.tag to 0. In all
 * cases, rd.tag is set to 0 if its bounds exceed rs1's bounds, rs1's tag
 * is 0  or rs1 is sealed.
 * YBNDSWI uses the top two bits of the immediate to determine decoding
 * of the remaining bits
 */
function clause execute (YBNDSWI(rd, rs1, uimm9)) = {
  let rs1_cap = Y(rs1);
  let length : CapLenBits = zero_extend(encdec_ybndsw_imm(uimm9));
  let newBase = rs1_cap.address;
  let newTop : CapLenBits = zero_extend(newBase) + length;
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(rs1_cap, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(rs1_cap, newBase, newTop);
  let cond = not(inBounds) |
             not(exact) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(rd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YBNDSW : (regidx, regidx, regidx)
/*!
 * insnref: ybndsw_32bit
 * Capability set bounds
 *
 * ybndsw rd, rs1, rs2
 * ybndswi rd, rs1, uimm
 *
 * Capability register rd  is set to capability register rs1  with the
 * base address of its bounds replaced with the value of rs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set rd.tag to 0. In all
 * cases, rd.tag is set to 0 if its bounds exceed rs1's bounds, rs1's tag
 * is 0  or rs1 is sealed.
 * YBNDSWI uses the s bit to scale the immediate by 4 places
 * immediate = ZeroExtend(s ? uimm<<4 : uimm)
 */
function clause execute (YBNDSW(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let length = X(rs2);
  let newBase = rs1_cap.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(rs1_cap, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(rs1_cap, newBase, newTop);
  let cond = not(inBounds & exact) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(rd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YMV : (regidx, regidx)
/*!
 * insnref: ymv_32bit
 * Capability move
 *
 * ymv rd, rs1
 *
 * The contents of capability register rs1  are written to capability
 * register rd. YMV unconditionally moves the whole capability to rd .
 */
function clause execute (YMV(rd, rs1)) = {
  Y(rd) = Y(rs1);
  RETIRE_SUCCESS
}

union clause ast = YBLD : (regidx, regidx, regidx)
/*!
 * insnref: ybld_32bit
 * Capability build
 *
 * ybld rd, rs1, rs2
 *
 * Copy rs2 to rd and set rd.tag to 1 if
 *
 * . rs1.tag is set, and
 * . rs1's bounds are not malformed, and all reserved fields are zero,
 * and
 * . rs1's permissions could have been legally produced by YPERMC, and
 * . rs1 is not sealed, and
 * . rs2's permissions and bounds are equal to or a subset of rs1's, and
 * . rs2's bounds are not malformed, and all reserved fields are zero,
 * and
 * . rs2's permissions could have been legally produced by YPERMC, and
 * . All reserved bits in rs2's metadata are 0;
 * Otherwise, copy rs2 to rd and clear rd's tag.
 * YBLD is typically used alongside PACKY to build capabilities from
 * integer values.
 */
function clause execute (YBLD(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_cap = Y(rs2);

  let tag = rs1_cap.tag &
            not(capIsSealed(rs1_cap)) &
            capIsSubset(rs2_cap, rs1_cap); /* Subset checks for malformed bounds,
                                              perms, and reserved bits */

  Y(rd) = { rs2_cap with tag = tag };
  RETIRE_SUCCESS
}

union clause ast = YSUNSEAL : (regidx, regidx, regidx)
/*!
 * insnref: ysunseal_32bit
 * Unseal by superset reconstruction
 *
 * ysunseal rd, rs1, rs2
 *
 * Copy rs2 to rd.
 *
 * Set rd's sealed field to 0.
 *
 * Set rd.tag to 1 if
 *
 * . rs1.tag is set, and
 * . rs1 passes all integrity checks, and
 * . rs1 is not sealed, and
 * . rs2.tag is set, and
 * . rs2 passes all integrity checks, and
 * . rs2 is sealed
 * . rs2's permissions and bounds are equal to or a subset of rs1's
 * Otherwise, clear rd's tag.
 */
function clause execute (YSUNSEAL(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_cap = Y(rs2);

  let new_cap = { rs2_cap with sealed=false };

  let tag = rs1_cap.tag &
            new_cap.tag &
            not(capIsSealed(rs1_cap)) &
            capIsSealed(new_cap) &
            capIsSubset(new_cap, rs1_cap); /* Subset checks for malformed bounds,
                                              perms, and reserved bits */

  Y(rd) = { new_cap with tag = tag };
  RETIRE_SUCCESS
}

union clause ast = YAMASK : (regidx, regidx)
/*!
 * insnref: yamask_32bit
 * Get Capability Representable Alignment Mask (YAMASK)
 *
 * yamask rd, rs1
 *
 * Integer register rd is set to a mask that can be used to round
 * addresses down to a value that is sufficiently aligned to set exact
 * bounds for the nearest representable length of rs1.
 */
function clause execute(YAMASK(rd, rs1)) = {
  let len = X(rs1);
  X(rd) = getRepresentableAlignmentMask(len);
  RETIRE_SUCCESS
}

union clause ast = YSS : (regidx, regidx, regidx)
/*!
 * insnref: yss_32bit
 * Capability test subset
 *
 * yss rd, rs1, rs2
 *
 * rd is set to 1 if the tag of capabilities rs1 and rs2 are equal and
 * the bounds and permissions of rs2 are a subset of those of rs1.
 * If either rs1 or rs2:
 *
 * . Have bounds which are malformed, or
 * . Have any bits set in reserved fields, or
 * . Have permissions that could not have been legally produced by YPERMC
 * then the instruction returns zero.
 */
function clause execute (YSS(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_cap = Y(rs2);

  X(rd) = zero_extend(bool_bits(
    (rs1_cap.tag == rs2_cap.tag) &
    capIsSubset(rs2_cap, rs1_cap) /* capIsSubset returns false if either input
                                     has malformed bounds, perms, or non-zero
                                     reserved bits */
  ));
  RETIRE_SUCCESS
}

union clause ast = YEQ : (regidx, regidx, regidx)
/*!
 * insnref: yeq_32bit
 * Set if Capabilities are EQual
 *
 * yeq rd, rs1, rs2
 *
 * rd is set to 1 if all bits (i.e. YLEN bits and the tag) of
 * capabilities rs1 and rs2  are equal, otherwise rd is set to 0.
 */
function clause execute (YEQ(rd, rs1, rs2)) = {
  let rs1_cap = Y(rs1);
  let rs2_cap = Y(rs2);
  X(rd) = zero_extend(bool_to_bits(rs1_cap == rs2_cap));
  RETIRE_SUCCESS
}

union clause ast = YSENTRY : (regidx, regidx)
/*!
 * insnref: ysentry_32bit
 * Seal capability as sealed entry.
 *
 * ysentry rd, rs1
 *
 * Capability `rd` is written with the capability in `rs1` with its type bit set to 1.
 * Attempting to seal an already sealed capability will lead to the tag of `rd` being set to 0.
 */
function clause execute (YSENTRY(rd, rs1)) = {
  let rs1_cap = Y(rs1);
  let inCap = clearTagIf(rs1_cap, capIsSealed(rs1_cap));
  Y(rd) = sealCap(inCap);
  RETIRE_SUCCESS
}

enum CapAccessType = { Cap_Read, Cap_Write, Cap_ReadWrite }

function cap_mem_access_authorised(auth_val : Capability, virtaddr(vaddr) : virtaddr, acc_type : CapAccessType) -> bool = {
  capTaggedAndNotMalformed(auth_val) &
  not(capIsSealed(auth_val)) &
  (match acc_type {
    Cap_Read => canR(auth_val),
    Cap_Write => canW(auth_val),
    Cap_ReadWrite => canR(auth_val) & canW(auth_val),
  }) : bool &
  (validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) &
  inCapBounds(auth_val, vaddr, cap_size)
}

function cap_mem_standard_errors(auth_val : Capability, vaddr : virtaddr, acc_type : CapAccessType) -> option(Retired) = {
  if not(cap_mem_access_authorised(auth_val, vaddr, acc_type)) then {
      handle_cheri_exception(match acc_type {
        Cap_Read => CapCheckType_Ld(),
        Cap_Write => CapCheckType_St(),
        Cap_ReadWrite => CapCheckType_St()
      } , vaddr);
      Some(RETIRE_FAIL)
  } else {
    // All loads and stores of capabilities must be aligned.
    if not(is_aligned_addr(vaddr, cap_size)) then {
      handle_mem_exception(vaddr, match acc_type {
        Cap_Read => E_Load_Access_Fault(),
        Cap_Write => E_SAMO_Access_Fault(),
        Cap_ReadWrite => E_SAMO_Access_Fault(),
      });
      Some(RETIRE_FAIL)
    } else {
      None()
    }
  }
}

union clause ast = LoadResCap : (regidx, regidx, bool, bool)
/*
 * insnref: load_res_cap_32bit modedep
 * Load Reserved Capability (LR.Y), 32-bit encodings
 *
 * lr.y rd, 0(rs1)
 *
 * Capability Pointer Mode:
 * Load reserved instructions, authorised by the capability in rs1. All
 * misaligned load reservations cause a load address misaligned exception
 * to allow software emulation (Zam extension, see citation).
 *
 * Integer Pointer Mode:
 * Load reserved instructions, authorised by the capability in ddc. All
 * misaligned load reservations cause a load address misaligned exception
 * to allow software emulation (Zam extension, see citation).
 */
function clause execute (LoadResCap(rd, rs1, aq, rl)) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1, zeros());

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Read) {
    Some(r) => r,
    None() => {
      // If we don't have C capability then the tag will always be cleared and
      // it is treated as an untagged load.
      match translateAddr(vaddr, Read(if canC(auth_val) then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, ext_ptw) => {
          let c = mem_read_cap(addr, pbmt, aq, aq & rl, false);
          match c {
            Ok(v) => {
              if v.tag & ext_ptw.tagged_load_behaviour == TaggedLoadTrap then {
                handle_translate_exception(vaddr, E_Load_Page_Fault());
                RETIRE_FAIL
              } else {
                load_reservation(physaddr_bits(addr));
                let cr = clearTagIf(v, ext_ptw.tagged_load_behaviour == TaggedLoadClear | not(canC(auth_val)));
                Y(rd) = legalizeLoadedPermissions(cr, auth_val);
                RETIRE_SUCCESS
              }
            },
            Err(e) => {
              handle_mem_exception(vaddr, e);
              RETIRE_FAIL
            },
          }
        }
      }
    },
  }
}

union clause ast = LoadCapImm : (regidx, regidx, bits(12))
/*!
 * insnref: load_32bit_cap modedep
 * Load capability
 *
 * Capability Pointer Mode:
 * ly rd, offset(rs1)
 *
 * Integer Pointer Mode:
 * ly rd, offset(rs1)
 *
 * Capability Pointer Mode:
 * Load a YLEN+1 bit value from memory and writes it to rd. The
 * capability in rs1 authorizes the operation. The effective address of
 * the memory access is obtained by adding the address of rs1 to the
 * sign-extended 12-bit offset. The tag value written to rd is 0 if the
 * tag of the memory location loaded is 0 or rs1 does not grant
 * C-permission.
 *
 * Integer Pointer Mode:
 * Loads a YLEN+1 bit value from memory and writes it to rd. The
 * capability authorising the operation is ddc. The effective address of
 * the memory access is obtained by adding rs1 to the sign-extended
 * 12-bit offset. The tag value written to rd is 0 if the tag of the
 * memory location loaded is 0 or ddc does not grant C-permission.
 */
function clause execute LoadCapImm(rd, rs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1, offset);

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Read) {
    Some(r) => r,
    None() => {
      // If we don't have C capability then the tag will always be cleared and
      // it is treated as an untagged load.
      match translateAddr(vaddr, Read(if canC(auth_val) then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, ext_ptw) => {
          let aq = false;
          let rl = false;
          match mem_read_cap(addr, pbmt, aq, aq & rl, false) {
            Ok(v) => {
              if v.tag & ext_ptw.tagged_load_behaviour == TaggedLoadTrap then {
                handle_translate_exception(vaddr, E_Load_Page_Fault());
                RETIRE_FAIL
              } else {
                let cr = clearTagIf(v, ext_ptw.tagged_load_behaviour == TaggedLoadClear | not(canC(auth_val)));
                Y(rd) = legalizeLoadedPermissions(cr, auth_val);
                RETIRE_SUCCESS
              }
            },
            Err(e) => {
              handle_mem_exception(vaddr, e);
              RETIRE_FAIL
            },
          }
        }
      }
    },
  }
}

union clause ast = StoreCapImm : (regidx, regidx, bits(12))
/*!
 * insnref: store_32bit_cap modedep
 * Store capability
 *
 * sy rs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Store the YLEN+1 bit value in rs2 to memory. The capability in rs1
 * authorizes the operation. The effective address of the memory access
 * is obtained by adding the address of rs1 to the sign-extended 12-bit
 * offset. The capability written to memory has the tag set to 0 if the
 * tag of rs2 is 0 or rs1 does not grant C-permission.
 *
 * Integer Pointer Mode:
 * Store the YLEN+1 bit value in rs2 to memory. The capability
 * authorising the operation is ddc. The effective address of the memory
 * access is obtained by adding rs1 to the sign-extended 12-bit offset.
 * The capability written to memory has the tag set to 0 if rs2's tag is
 * 0 or ddc does not grant C-permission.
 */
function clause execute StoreCapImm(rs2, rs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1, offset);

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Write) {
    Some(r) => r,
    None() => {
      let rs2_cap = Y(rs2);
      let rs2_cap = clearTagIf(rs2_cap, not(canC(auth_val)));
      let rs2_cap = legalizeStoredPermissions(rs2_cap, auth_val);

      match translateAddr(vaddr, Write(if rs2_cap.tag then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, _) => {
          let aq = false;
          let rl = false;
          match mem_write_ea_cap(addr, aq & rl, rl, false) {
            Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            Ok(_)  => {
              match mem_write_cap(addr, pbmt, rs2_cap, aq & rl, rl, false) {
                Ok(true)  => RETIRE_SUCCESS,
                Ok(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                Err(e)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
              }
            }
          }
        }
      }
    },
  }
}

union clause ast = StoreCondCap : (regidx, regidx, regidx, bool, bool)
/*!
 * insnref: store_cond_cap_32bit modedep
 * Store Conditional (SC.Y), 32-bit encoding
 *
 * sc.y rd, rs2, 0(rs1)
 *
 * Capability Pointer Mode:
 * Store conditional instructions, authorised by the capability in rs1.
 * All misaligned store conditionals cause a store/AMO address misaligned
 * exception to allow software emulation (Zam extension, see citation).
 *
 * Integer Pointer Mode:
 * Store conditional instructions, authorised by the capability in ddc.
 * All misaligned store conditionals cause a store/AMO address misaligned
 * exception to allow software emulation (Zam extension, see citation).
 */
function clause execute StoreCondCap(rd, rs2, rs1, aq, rl) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1, zeros());

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Write) {
    Some(r) => r,
    None() => {
      let rs2_cap = Y(rs2);
      let rs2_cap = clearTagIf(rs2_cap, not(canC(auth_val)));
      let rs2_cap = legalizeStoredPermissions(rs2_cap, auth_val);

      match translateAddr(vaddr, Write(if rs2_cap.tag then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, _) => {
          if not(match_reservation(physaddr_bits(addr))) then {
            /* cannot happen in rmem */
            X(rd) = zero_extend(0b1);
            cancel_reservation();
            RETIRE_SUCCESS
          } else {
            match mem_write_ea_cap(addr, aq & rl, rl, false) {
              Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
              Ok(_)  => {
                match mem_write_cap(addr, pbmt, rs2_cap, aq & rl, rl, false) {
                  Ok(true) => {
                    X(rd) = zero_extend(0b0);
                    cancel_reservation();
                    RETIRE_SUCCESS
                  },
                  Ok(false) => {
                    X(rd) = zero_extend(0b1);
                    cancel_reservation();
                    RETIRE_SUCCESS
                  },
                  Err(e) => {
                    handle_mem_exception(vaddr, e);
                    RETIRE_FAIL
                  }
                }
              }
            }
          }
        }
      }
    },
  }
}

union clause ast = AMOSwapCap : (regidx, regidx, regidx, bool, bool)
/*!
 * insnref: amoswap_32bit_cap modedep
 * Atomic Operation (AMOSWAP.Y), 32-bit encoding
 *
 * amoswap.y rd, rs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in rs1.
 *
 * Integer Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in ddc.
 */
function clause execute AMOSwapCap(rd, rs2, rs1, aq, rl) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1, zeros());

  match cap_mem_standard_errors(auth_val, vaddr, Cap_ReadWrite) {
    Some(r) => r,
    None() => {
      let rs2_cap = Y(rs2);
      let rs2_cap = clearTagIf(rs2_cap, not(canC(auth_val)));
      let rs2_cap = legalizeStoredPermissions(rs2_cap, auth_val);

      match translateAddr(vaddr, ReadWrite(if canC(auth_val) then Tagged else Data, if rs2_cap.tag then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, ext_ptw) => {
          match mem_write_ea_cap(addr, aq & rl, rl, false) {
            Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            Ok(_)  => {
              match mem_read_cap(addr, pbmt, aq, aq & rl, false) {
                Ok(v) => {
                  match mem_write_cap(addr, pbmt, rs2_cap, aq & rl, rl, false) {
                    Ok(_) => {
                      if v.tag & ext_ptw.tagged_load_behaviour == TaggedLoadTrap then {
                        handle_translate_exception(vaddr, E_Load_Page_Fault());
                        RETIRE_FAIL
                      } else {
                        let cr = clearTagIf(v, ext_ptw.tagged_load_behaviour == TaggedLoadClear | not(canC(auth_val)));
                        Y(rd) = legalizeLoadedPermissions(cr, auth_val);
                        RETIRE_SUCCESS
                      }
                    },
                    Err(e) => {
                      handle_mem_exception(vaddr, e);
                      RETIRE_FAIL
                    },
                  }
                },
                Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
              }
            }
          }
        }
      }
    },
  }
}

/* Zero arg */

mapping pointer_mode_funct5 : PointerMode <-> bits(5) = {
  CapPtrMode <-> 0b00000,
  IntPtrMode <-> 0b00001,
}

mapping clause encdec = YMODESW(mode)                                               if cheri_registers_enabled()
  <-> 0b0101011 @ pointer_mode_funct5(mode) @ 0b00000 @ 0b000 @ 0b00000 @ 0b1111011 if cheri_registers_enabled()

mapping pointer_mode_mnemonic : PointerMode <-> string = {
  CapPtrMode <-> "y",
  IntPtrMode <-> "i",
}

mapping clause assembly = YMODESW(mode) <-> "ymodesw." ^ pointer_mode_mnemonic(mode)

/* Two arg */

mapping clause encdec = YMODER(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00111 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YTYPER(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00101 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YPERMR(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00001 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YBASER(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00000 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YTOPR(rd, rs1)                                           if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00010 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YLENR(rd, rs1)                                           if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00011 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YTAGR(rd, rs1)                                           if cheri_registers_enabled()
  <-> 0b1111010 @ 0b00100 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause encdec = SRLIY(rd, rs1)                                           if cheri_registers_enabled() & xlen == 64
  <-> 0b00000 @ 0b1000000 @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & xlen == 64
mapping clause encdec = SRLIY(rd, rs1)                                           if cheri_registers_enabled() & xlen == 32
  <-> 0b00000 @ 0b0100000 @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & xlen == 32

mapping clause encdec = YMV(rd, rs1)                                             if cheri_registers_enabled()
  <-> 0b0000011 @ 0b00000 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YSENTRY(rd, rs1)                                         if cheri_registers_enabled()
  <-> 0b0011011 @ 0b00000 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause encdec = YAMASK(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b1111000 @ 0b00000 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause assembly = YMODER(rd, rs1)  <-> "ymoder"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YTYPER(rd, rs1)  <-> "ytyper"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YPERMR(rd, rs1)  <-> "ypermr"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YBASER(rd, rs1)  <-> "ybaser"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YTOPR(rd, rs1)   <-> "ytopr"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YLENR(rd, rs1)   <-> "ylenr"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = YTAGR(rd, rs1)   <-> "ytagr"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)
mapping clause assembly = SRLIY(rd, rs1)                                              if xlen == 32
  <-> "srliy"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1) ^ sep() ^ "32" if xlen == 32
mapping clause assembly = SRLIY(rd, rs1)                                              if xlen == 64
  <-> "srliy"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1) ^ sep() ^ "64" if xlen == 64

mapping clause assembly = YMV(rd, rs1)     <-> "ymv"     ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = YSENTRY(rd, rs1) <-> "ysentry" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = YAMASK(rd, rs1)  <-> "yamask"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)

/* Three arg */

mapping clause encdec = YPERMC(rd, rs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0010011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YMODEW(rd, rs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0101011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YADDRW(rd, rs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0001011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = PACKY(rd, rs1, rs2)                                              if cheri_registers_enabled()
  <-> 0b0000001 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YADD(rd, rs1, rs2)                                               if cheri_registers_enabled() & (rs2 != zreg)
  <-> 0b0000011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & (rs2 != zreg)
mapping clause encdec = YBNDSRW(rd, rs1, rs2)                                            if cheri_registers_enabled()
  <-> 0b0100011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YBNDSW(rd, rs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0011011 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YBLD(rd, rs1, rs2)                                               if cheri_registers_enabled()
  <-> 0b0001111 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YSUNSEAL(rd, rs1, rs2)                                           if cheri_registers_enabled()
  <-> 0b0000111 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause encdec = YEQ(rd, rs1, rs2)                                                if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YSS(rd, rs1, rs2)                                                if cheri_registers_enabled()
  <-> 0b0001110 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause encdec = YADDI(rd, rs1, imm12)                                 if cheri_registers_enabled()
  <-> imm12 : bits(12) @ encdec_reg(rs1) @ 0b100 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()
mapping clause encdec = YBNDSWI(rd, rs1, uimm9)                                      if cheri_registers_enabled()
  <-> 0b111 @ uimm9 : bits(9) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled()

mapping clause assembly = YPERMC(rd, rs1, rs2)   <-> "ypermc"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YMODEW(rd, rs1, rs2)   <-> "ymodew"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YADDRW(rd, rs1, rs2)   <-> "yaddrw"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = PACKY(rd, rs1, rs2)    <-> "packy"    ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YADD(rd, rs1, rs2)     <-> "yadd"     ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBNDSRW(rd, rs1, rs2)  <-> "ybndsrw"  ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBNDSW(rd, rs1, rs2)   <-> "ybndsw"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBLD(rd, rs1, rs2)     <-> "ybld"     ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YSUNSEAL(rd, rs1, rs2) <-> "ysunseal" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = YEQ(rd, rs1, rs2)     <-> "yeq"     ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YSS(rd, rs1, rs2)     <-> "yss"     ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = YADDI(rd, rs1, imm12) <-> "yaddi"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = YBNDSWI(rd, rs1, uimm9) <-> "ybndswi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_16(0b000 @ encdec_ybndsw_imm(uimm9))

/* Loads and stores */

let haveRV128 = xlen >= 128
let haveRV64  = xlen >= 64

mapping clause encdec = LoadCapImm(rd, rs1, offset)                 if cheri_registers_enabled() & (rs1 != zreg | effective_cheri_mode() == IntPtrMode) /* ly */
  <-> offset @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & (rs1 != zreg | effective_cheri_mode() == IntPtrMode)

mapping clause encdec = StoreCapImm(rs2, rs1, off7 @ off5)                                    if cheri_registers_enabled() & (rs1 != zreg)
  <-> off7 : bits(7) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b010 @ off5 : bits(5) @ 0b1111011 if cheri_registers_enabled() & (rs1 != zreg) /* sy */

mapping clause assembly = LoadCapImm(rd, rs1, offset)   <-> "ly" ^ spc() ^ reg_name(rd)  ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(rs2, rs1, offset) <-> "sy" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

mapping clause encdec = LoadResCap(rd, rs1, aq, rl)                                                            if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & (rs1 != zreg | effective_cheri_mode() == IntPtrMode)
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & (rs1 != zreg | effective_cheri_mode() == IntPtrMode) /* lr.y */

mapping clause encdec = StoreCondCap(rd, rs2, rs1, aq, rl)                                                             if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & (rs1 != zreg | effective_cheri_mode() == IntPtrMode)
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & (rs1 != zreg | effective_cheri_mode() == IntPtrMode) /* sc.y */

mapping clause encdec = AMOSwapCap(rd, rs2, rs1, aq, rl)                                                               if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo)
  <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b1111011 if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) /* amoswap.y */

mapping clause assembly = LoadResCap(rd, rs1, aq, rl)        <-> "lr.y"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = StoreCondCap(rd, rs2, rs1, aq, rl) <-> "sc.y"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs2) ^ sep() ^ reg_name(rs1)
mapping clause assembly = AMOSwapCap(rd, rs2, rs1, aq, rl)   <-> "amoswap.y" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2) ^ sep() ^ reg_name(rs1)

/*
  CHERI really needs sub word atomic operations because bounds checks mean you
  can't implement them in software with word sized operations. The RISC-V
  spec. does not define lr / sc for bytes or half words although the obvious
  encodings are vacant. Since the base Sail model actually implements the unused
  widths but refuses to decode them we can implement them for CHERI simply by
  adding the decodings here.
*/
mapping clause encdec = LOADRES(aq, rl, rs1, size, rd)                                                                                if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ encdec_reg(rs1) @ 0b0 @ size_enc(size) @ encdec_reg(rd) @ 0b0101111         if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
mapping clause encdec = STORECON(aq, rl, rs2, rs1, size, rd)                                                                          if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b0 @ size_enc(size) @ encdec_reg(rd) @ 0b0101111 if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))

/*
 * Encoding/assembly mappings for capmode specific instructions. This does not
 * include loads/stores since they are not decoded differently, but instead
 * use hooks for semantic differences.
 */
mapping clause encdec_capmode = AUIPC_capmode(imm, rd)
  <-> imm @ encdec_reg(rd) @ 0b0010111
mapping clause assembly = AUIPC_capmode(imm, rd)
  <-> "auipc" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_20(imm)
mapping clause encdec_capmode = JALR_capmode(imm, rs1, rd)
  <-> imm @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b1100111
mapping clause assembly = JALR_capmode(imm, rs1, rd)
  <-> "jalr" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)
/* See `mapping clause encdec = RISCV_JAL` for why we have to use this syntax */
mapping clause encdec_capmode = JAL_capmode(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, rd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ encdec_reg(rd) @ 0b1101111
mapping clause assembly = JAL_capmode(imm, rd)
  <-> "jal" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_21(imm)

mapping clause encdec_capmode = BEQ_reserved_capmode(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1)                                 if encdec_reg(rs1) <=_u encdec_reg(rs2)
  <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011 if encdec_reg(rs1) <=_u encdec_reg(rs2)
mapping clause assembly = BEQ_reserved_capmode (imm, rs1, rs2)
  <-> "reserved (beq" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_13(imm) ^ ")"
mapping clause encdec_capmode = BNE_reserved_capmode(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1)                                 if encdec_reg(rs1) <=_u encdec_reg(rs2)
  <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b001 @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011 if encdec_reg(rs1) <=_u encdec_reg(rs2)
mapping clause assembly = BNE_reserved_capmode (imm, rs1, rs2)
  <-> "reserved (bne" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_13(imm) ^ ")"
