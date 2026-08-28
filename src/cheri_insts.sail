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
 * auipc cd, imm
 *
 * Form a 32-bit offset from the 20-bit immediate filling the lowest 12
 * bits with zeros. Increment the address of the AUIPC instruction's pcc
 * by the 32-bit offset, then write the output capability to cd. The tag
 * bit of the output capability is 0 if the incremented address is
 * outside the pcc's Representable Range.
 */
function clause execute AUIPC_capmode(imm, cd) = {
  let off : xlenbits = sign_extend(imm @ 0x000);
  let (representable, newCap) = setCapAddr(PCC, PC + off);
  Y(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}

union clause ast = JAL_capmode : (bits(21), regidx)
/*!
 * insnref: jal_32bit capmode
 * Jump and link
 *
 * jal cd, offset
 *
 * JAL's immediate encodes a signed offset in multiple of 2 bytes. The
 * pcc is incremented by the sign-extended offset to form the jump target
 * capability. The target capability is written to pcc. The pcc of the
 * next instruction following the jump is sealed and written to cd.
 */
function clause execute(JAL_capmode(imm, cd)) = {
  let off : xlenbits = sign_extend(imm);
  let newPC = PC + off;
  if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(virtaddr(newPC), E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    Y(cd) = sealCap(linkCap);
    set_next_pc(newPC);
    RETIRE_SUCCESS
  }
}

union clause ast = JALR_capmode : (bits(12), regidx, regidx)
/*!
 * insnref: jalr_32bit capmode
 * Jump and link register
 *
 * jalr cd, cs1, offset
 *
 * JALR allows unconditional, indirect jumps to a target capability. The
 * target capability is unsealed if the offset is zero. The target
 * address is obtained by adding the sign-extended 12-bit offset to
 * cs1.address, then setting the least-significant bit of the result to
 * zero. The target capability may have Invalid address conversion
 * performed and is then installed in pcc. The pcc of the next
 * instruction following the jump is sealed and written to cd.
 */
function clause execute(JALR_capmode(imm, cs1, cd)) = {
  let cs1_val = Y(cs1);

  // Calculate new PC which may be offset from the capability address.
  let off : xlenbits = sign_extend(imm);
  let newPC = [cs1_val.address + off with 0 = bitzero]; /* clear bit zero as for RISCV JALR */

  if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(virtaddr(newPC), E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    Y(cd) = sealCap(linkCap);
    set_next_pc(newPC);

    // Construct the new capability pointing to the address + offset.
    let (representable, newPCC) = setCapAddr(cs1_val, newPC);
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
union clause ast = YLENR  : (regidx, regidx)
union clause ast = YTAGR  : (regidx, regidx)
union clause ast = YHIR   : (regidx, regidx)
union clause ast = YMODER : (regidx, regidx)
union clause ast = YTYPER : (regidx, regidx)

/*!
 * insnref: ymoder_32bit brief
 * Capability get CHERI execution mode
 *
 * ymoder rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (YMODER(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = zero_extend(execution_mode_encdec(getCapMode(capVal)));
  RETIRE_SUCCESS
}

/*!
 * insnref: ytyper_32bit brief
 * Capability get type
 *
 * ytyper rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (YTYPER(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = zero_extend(bool_to_bits(capVal.sealed));
  RETIRE_SUCCESS
}

/*!
 * insnref: ypermr_32bit brief
 * Capability get permissions
 *
 * ypermr rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (YPERMR(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = packPerms(getArchPermsLegalized(capVal), capVal.cl, capVal.sd_perms).bits;
  RETIRE_SUCCESS
}

/*!
 * insnref: ybaser_32bit
 * Capability get base address
 *
 * ybaser rd, cs1
 *
 * Decode the base integer address from cs1's bounds and write the result
 * to rd. It is not required that the input capability cs1  has its tag
 * set to 1.
 */

function clause execute (YBASER(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = match getCapBoundsBits(capVal) {
    None() => zeros(),
    Some(base, _) => base
  };
  RETIRE_SUCCESS
}

/*!
 * insnref: yhir_32bit
 * Capability get metadata
 *
 * yhir rd, cs1
 *
 * Copy the metadata (bits [YLEN-1:MXLEN]) of capability cs1 into rd.
 */
function clause execute (YHIR(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = capToMetadataBits(capVal).bits;
  RETIRE_SUCCESS
}

union clause ast = YHIW : (regidx, regidx, regidx)
/*!
 * insnref: yhiw_32bit
 * Capability set metadata
 *
 * yhiw cd, cs1, rs2
 *
 * Copy cs1  to cd , replace the capability metadata (i.e. bits
 * [YLEN-1:MXLEN]) with rs2  and set cd.tag to 0.
 */
function clause execute (YHIW(cd, cs1, rs2)) = {
  let capVal = Y(cs1);
  let intVal = X(rs2);
  let newCap = bitsToCap(false, intVal @ capVal.address);
  Y(cd) = newCap;
  RETIRE_SUCCESS
}

/*!
 * insnref: ylenr_32bit
 * Capability get length
 *
 * ylenr rd, cs1
 *
 * Calculate the length of cs1's bounds and write the result in rd. The
 * length is defined as the difference between the decoded bounds' top
 * and base addresses i.e. top - base. It is not required that the input
 * capability cs1  has its tag set to 1. YLENR outputs 0 if cs1's bounds
 * are malformed (see Malformed Capability Bounds), and 2^MXLEN^-1 if the
 * length of cs1 is 2^MXLEN^.
 */
function clause execute (YLENR(rd, cs1)) = {
  let capVal = Y(cs1);
  // getCapLength returns 0 if the bounds are malformed
  let len = getCapLength(capVal);
  X(rd) = to_bits(xlen, if len > cap_max_addr then cap_max_addr else len);
  RETIRE_SUCCESS
}

/*!
 * insnref: ytagr_32bit
 * Capability get tag
 *
 * ytagr rd, cs1
 *
 * Zero extend the value of cs1.tag and write the result to rd.
 */
function clause execute (YTAGR(rd, cs1)) = {
  let capVal = Y(cs1);
  X(rd) = zero_extend(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

union clause ast = YPERMC : (regidx, regidx, regidx)
/*!
 * insnref: ypermc_32bit brief
 * Mask capability permissions
 *
 * ypermc cd, cs1, rs2
 *
 * See ISA document for full description
 */
function clause execute(YPERMC(cd, cs1, rs2)) = {
  let cs1_val = Y(cs1);
  let rs2_val = X(rs2);

  let cond = capIsSealed(cs1_val) | capIsMalformed(cs1_val);
  let inCap = clearTagIf(cs1_val, cond);

  let old_perms = packPerms(getArchPermsLegalized(inCap), inCap.cl, inCap.sd_perms).bits;

  let new_perms = old_perms & rs2_val;

  let (new_arch_perms, new_cl, new_sd_perms) = unpackPerms(struct {bits = new_perms});
  let newCap = { setArchPerms(inCap, new_arch_perms) with cl = new_cl, sd_perms = new_sd_perms };

  Y(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YMODEW : (regidx, regidx, regidx)
/*!
 * insnref: ymodew_32bit
 * Capability set CHERI execution mode
 *
 * ymodew cd, cs1, rs2
 *
 * Copy cs1 to cd. Clear cd.tag if cs1 is sealed. Update the M-bit of cd
 * to the least significant bit of rs2 if the two following conditions
 * are met, otherwise do not update it:
 * . X-permission is set
 * . The existing permissions can be produced by YPERMC
 */
function clause execute(YMODEW(cd, cs1, rs2)) = {
  let cap = Y(cs1);
  let mode = execution_mode_encdec(X(rs2)[0 .. 0]);

  let cap = clearTagIf(cap, capIsSealed(cap));
  let hasMode = not(permsMalformed(cap)) & canX(cap);
  let newCap = if hasMode then setCapMode(cap, mode) else cap;

  Y(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YMODESW : (ExecutionMode)
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
 *   M-bit in pcc is set to _Capability Pointer Mode_ (0). Otherwise no effect.
 * * YMODESWI: If the current mode in pcc is _Capability Pointer Mode_ (0), then the M-bit
 *   in pcc is set to _Integer Pointer Mode_ (1). Otherwise no effect.
 *
 * Executing YMODESWY or YMODESWI from the program buffer in debug mode updates
 * the M-bit of dinfc. The M-bit of dinfc sets the CHERI execution mode for the execution
 * of the next instruction from the program buffer, and is used to control which CHERI
 * execution mode to enter next time debug mode is entered. The CHERI execution mode
 * is only controlled by the M-bit of dinfc in debug mode.
 */
function clause execute(YMODESW(mode)) = {
  if getCapMode(PCC) != mode then {
    set_next_pcc(setCapMode(PCC, mode));
  };
  // if debug_mode_active then dinfc = setCapMode(infinite_cap, mode);
  RETIRE_SUCCESS
}

union clause ast = ADDY : (regidx, regidx, regidx)
/*!
 * insnref: addy_32bit
 * Capability pointer increment
 *
 * addy cd, cs1, rs2
 * addiy cd, cs1, imm
 *
 * Increment the address field of the capability cs1  and write the
 * result to cd . The tag bit of the output capability is 0 if cs1  did
 * not have its tag set to 1, the incremented address is outside cs1's
 * Representable Range or cs1  is sealed.
 *
 * For ADDY, the address is incremented by the value in rs2 .
 * For ADDIY, the address is incremented by the immediate value imm.
 */
function clause execute (ADDY(cd, cs1, rs2)) = {
  let cs1_val = Y(cs1);
  let rs2_val = X(rs2);

  let newCap = incCapAddrChecked(cs1_val, rs2_val);

  Y(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = ADDIY : (regidx, regidx, bits(12))
/*!
 * insnref: addy_32bit
 * Capability pointer increment
 *
 * addy cd, cs1, rs2
 * addiy cd, cs1, imm
 *
 * Increment the address field of the capability cs1  and write the
 * result to cd . The tag bit of the output capability is 0 if cs1  did
 * not have its tag set to 1, the incremented address is outside cs1's
 * Representable Range or cs1  is sealed.
 *
 * For ADDY, the address is incremented by the value in rs2 .
 * For ADDIY, the address is incremented by the immediate value imm.
 */
function clause execute (ADDIY(cd, cs1, imm)) = {
  let cs1_val = Y(cs1);
  let immBits : xlenbits = sign_extend(imm);

  let newCap = incCapAddrChecked(cs1_val, immBits);

  Y(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = YADDRW : (regidx, regidx, regidx)
/*!
 * insnref: yaddrw_32bit
 * Capability set address
 *
 * yaddrw cd, cs1, rs2
 *
 * Set the address field of capability cs1 to rs2 and write the output
 * capability to cd. The tag bit of the output capability is 0 if cs1 did
 * not have its tag set to 1, rs2 is outside the Representable Range of
 * cs1 or if cs1 is sealed.
 */
function clause execute (YADDRW(cd, cs1, rs2)) = {
  Y(cd) = setCapAddrChecked(Y(cs1), X(rs2));
  RETIRE_SUCCESS
}

union clause ast = YBNDSRW : (regidx, regidx, regidx)
/*!
 * insnref: ybndsrw_32bit
 * Capability set bounds, rounding up if necessary
 *
 * ybndsrw cd, cs1, rs2
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address
 * field and the length of its bounds set to rs2. The base is rounded
 * down and the length is rounded up by the smallest amount needed to
 * form a representable capability covering the requested bounds. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0 or cs1  is sealed.
 */
function clause execute (YBNDSRW(cd, cs1, rs2)) = {
  let cs1_val = Y(cs1);
  let length = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (_, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  let cond = not(inBounds) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YBNDSIW : (regidx, regidx, bits(1), bits(5))
/*!
 * insnref: ybndsw_32bit
 * Capability set bounds
 *
 * ybndsw cd, cs1, rs2
 * ybndsiw cd, cs1, uimm
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set cd.tag to 0. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0  or cs1 is sealed.
 * YBNDSIW uses the s bit to scale the immediate by 4 places
 * immediate = ZeroExtend(s ? uimm<<4 : uimm)
 */
function clause execute (YBNDSIW(cd, cs1, s, uimm5)) = {
  let cs1_val = Y(cs1);
  let length = if s == 0b1 then uimm5 @ 0b0000 else 0b0000 @ uimm5;
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  assert(exact, "YBNDSIW immediate too small for non-exact lengths");
  let cond = not(inBounds) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YBNDSW : (regidx, regidx, regidx)
/*!
 * insnref: ybndsw_32bit
 * Capability set bounds
 *
 * ybndsw cd, cs1, rs2
 * ybndsiw cd, cs1, uimm
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set cd.tag to 0. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0  or cs1 is sealed.
 * YBNDSIW uses the s bit to scale the immediate by 4 places
 * immediate = ZeroExtend(s ? uimm<<4 : uimm)
 */
function clause execute (YBNDSW(cd, cs1, rs2)) = {
  let cs1_val = Y(cs1);
  let length = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  let cond = not(inBounds & exact) |
             capIsMalformed(newCap) |
             capIsSealed(newCap);
  Y(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = YMV : (regidx, regidx)
/*!
 * insnref: ymv_32bit
 * Capability move
 *
 * ymv cd, cs1
 *
 * The contents of capability register cs1  are written to capability
 * register cd. YMV unconditionally moves the whole capability to cd .
 */
function clause execute (YMV(cd, cs1)) = {
  Y(cd) = Y(cs1);
  RETIRE_SUCCESS
}

union clause ast = YBLD : (regidx, regidx, regidx)
/*!
 * insnref: ybld_32bit
 * Capability build
 *
 * ybld cd, cs1, cs2
 *
 * Copy cs2 to cd and set cd.tag to 1 if
 *
 * . cs1.tag is set, and
 * . cs1's bounds are not malformed, and all reserved fields are zero,
 * and
 * . cs1's permissions could have been legally produced by YPERMC, and
 * . cs1 is not sealed, and
 * . cs2's permissions and bounds are equal to or a subset of cs1's, and
 * . cs2's bounds are not malformed, and all reserved fields are zero,
 * and
 * . cs2's permissions could have been legally produced by YPERMC, and
 * . All reserved bits in cs2's metadata are 0;
 * Otherwise, copy cs2 to cd and clear cd's tag.
 * YBLD is typically used alongside YHIW to build capabilities from
 * integer values.
 */
function clause execute (YBLD(cd, cs1, cs2)) = {
  let cs1_val = Y(cs1);
  let cs2_val = Y(cs2);

  let tag = cs1_val.tag &
            not(capIsSealed(cs1_val)) &
            capIsSubset(cs2_val, cs1_val); /* Subset checks for malformed bounds,
                                              perms, and reserved bits */

  Y(cd) = { cs2_val with tag = tag };
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

union clause ast = YLT : (regidx, regidx, regidx)
/*!
 * insnref: ylt_32bit
 * Capability test subset
 *
 * ylt rd, cs1, cs2
 *
 * rd is set to 1 if the tag of capabilities cs1 and cs2 are equal and
 * the bounds and permissions of cs2 are a subset of those of cs1.
 * If either cs1 or cs2:
 *
 * . Have bounds which are malformed, or
 * . Have any bits set in reserved fields, or
 * . Have permissions that could not have been legally produced by YPERMC
 * then the instruction returns zero.
 */
function clause execute (YLT(rd, cs1, cs2)) = {
  let cs1_val = Y(cs1);
  let cs2_val = Y(cs2);

  X(rd) = zero_extend(bool_bits(
    (cs1_val.tag == cs2_val.tag) &
    capIsSubset(cs2_val, cs1_val) /* capIsSubset returns false if either input
                                     has malformed bounds, perms, or non-zero
                                     reserved bits */
  ));
  RETIRE_SUCCESS
}

union clause ast = SYEQ : (regidx, regidx, regidx)
/*!
 * insnref: syeq_32bit
 * Set if Capabilities are EQual
 *
 * syeq rd, cs1, cs2
 *
 * rd is set to 1 if all bits (i.e. YLEN bits and the tag) of
 * capabilities cs1 and cs2  are equal, otherwise rd is set to 0.
 */
function clause execute (SYEQ(rd, cs1, cs2)) = {
  let cs1_val = Y(cs1);
  let cs2_val = Y(cs2);
  X(rd) = zero_extend(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

union clause ast = YSENTRY : (regidx, regidx)
/*!
 * insnref: ysentry_32bit
 * Seal capability as sealed entry.
 *
 * ysentry cd, cs1
 *
 * Capability `cd` is written with the capability in `cs1` with its type bit set to 1.
 * Attempting to seal an already sealed capability will lead to the tag of `cd` being set to 0.
 */
function clause execute (YSENTRY(cd, cs1)) = {
  let cs1_val = Y(cs1);
  let inCap = clearTagIf(cs1_val, capIsSealed(cs1_val));
  Y(cd) = sealCap(inCap);
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
 * Capability Pointer Mode:
 * lr.y cd, 0(cs1)
 *
 * Integer Pointer Mode:
 * lr.y cd, 0(rs1)
 *
 * Capability Pointer Mode:
 * Load reserved instructions, authorised by the capability in cs1. All
 * misaligned load reservations cause a load address misaligned exception
 * to allow software emulation (Zam extension, see citation).
 *
 * Integer Pointer Mode:
 * Load reserved instructions, authorised by the capability in ddc. All
 * misaligned load reservations cause a load address misaligned exception
 * to allow software emulation (Zam extension, see citation).
 */
function clause execute (LoadResCap(cd, rs1_cs1, aq, rl)) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, zeros());

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
                Y(cd) = legalizeLoadedPermissions(cr, auth_val);
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
 * ly cd, offset(cs1)
 *
 * Integer Pointer Mode:
 * ly cd, offset(rs1)
 *
 * Capability Pointer Mode:
 * Load a YLEN+1 bit value from memory and writes it to cd. The
 * capability in cs1 authorizes the operation. The effective address of
 * the memory access is obtained by adding the address of cs1 to the
 * sign-extended 12-bit offset. The tag value written to cd is 0 if the
 * tag of the memory location loaded is 0 or cs1 does not grant
 * C-permission.
 *
 * Integer Pointer Mode:
 * Loads a YLEN+1 bit value from memory and writes it to cd. The
 * capability authorising the operation is ddc. The effective address of
 * the memory access is obtained by adding rs1 to the sign-extended
 * 12-bit offset. The tag value written to cd is 0 if the tag of the
 * memory location loaded is 0 or ddc does not grant C-permission.
 */
function clause execute LoadCapImm(cd, rs1_cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, offset);

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
                Y(cd) = legalizeLoadedPermissions(cr, auth_val);
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
 * Capability Pointer Mode:
 * sy cs2, offset(cs1)
 *
 * Integer Pointer Mode:
 * sy cs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Store the YLEN+1 bit value in cs2 to memory. The capability in cs1
 * authorizes the operation. The effective address of the memory access
 * is obtained by adding the address of cs1 to the sign-extended 12-bit
 * offset. The capability written to memory has the tag set to 0 if the
 * tag of cs2 is 0 or cs1 does not grant C-permission.
 *
 * Integer Pointer Mode:
 * Store the YLEN+1 bit value in cs2 to memory. The capability
 * authorising the operation is ddc. The effective address of the memory
 * access is obtained by adding rs1 to the sign-extended 12-bit offset.
 * The capability written to memory has the tag set to 0 if cs2's tag is
 * 0 or ddc does not grant C-permission.
 */
function clause execute StoreCapImm(cs2, rs1_cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, offset);

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Write) {
    Some(r) => r,
    None() => {
      let cs2_val = Y(cs2);
      let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));
      let cs2_val = legalizeStoredPermissions(cs2_val, auth_val);

      match translateAddr(vaddr, Write(if cs2_val.tag then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, _) => {
          let aq = false;
          let rl = false;
          match mem_write_ea_cap(addr, aq & rl, rl, false) {
            Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            Ok(_)  => {
              match mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false) {
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
 * Capability Pointer Mode:
 * sc.y rd, cs2, 0(cs1)
 *
 * Integer Pointer Mode:
 * sc.y rd, cs2, 0(rs1)
 *
 * Capability Pointer Mode:
 * Store conditional instructions, authorised by the capability in cs1.
 * All misaligned store conditionals cause a store/AMO address misaligned
 * exception to allow software emulation (Zam extension, see citation).
 *
 * Integer Pointer Mode:
 * Store conditional instructions, authorised by the capability in ddc.
 * All misaligned store conditionals cause a store/AMO address misaligned
 * exception to allow software emulation (Zam extension, see citation).
 */
function clause execute StoreCondCap(rd, cs2, rs1_cs1, aq, rl) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, zeros());

  match cap_mem_standard_errors(auth_val, vaddr, Cap_Write) {
    Some(r) => r,
    None() => {
      let cs2_val = Y(cs2);
      let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));
      let cs2_val = legalizeStoredPermissions(cs2_val, auth_val);

      match translateAddr(vaddr, Write(if cs2_val.tag then Tagged else Data)) {
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
                match mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false) {
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
 * Capability Pointer Mode:
 * amoswap.y cd, cs2, offset(cs1)
 *
 * Integer Pointer Mode:
 * amoswap.y cd, cs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in cs1.
 *
 * Integer Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in ddc.
 */
function clause execute AMOSwapCap(cd, cs2, rs1_cs1, aq, rl) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, zeros());

  match cap_mem_standard_errors(auth_val, vaddr, Cap_ReadWrite) {
    Some(r) => r,
    None() => {
      let cs2_val = Y(cs2);
      let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));
      let cs2_val = legalizeStoredPermissions(cs2_val, auth_val);

      match translateAddr(vaddr, ReadWrite(if canC(auth_val) then Tagged else Data, if cs2_val.tag then Tagged else Data)) {
        TR_Failure(e, _) => { handle_translate_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, pbmt, ext_ptw) => {
          match mem_write_ea_cap(addr, aq & rl, rl, false) {
            Err(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            Ok(_)  => {
              match mem_read_cap(addr, pbmt, aq, aq & rl, false) {
                Ok(v) => {
                  match mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false) {
                    Ok(_) => {
                      if v.tag & ext_ptw.tagged_load_behaviour == TaggedLoadTrap then {
                        handle_translate_exception(vaddr, E_Load_Page_Fault());
                        RETIRE_FAIL
                      } else {
                        let cr = clearTagIf(v, ext_ptw.tagged_load_behaviour == TaggedLoadClear | not(canC(auth_val)));
                        Y(cd) = legalizeLoadedPermissions(cr, auth_val);
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

mapping execution_mode_funct7 : ExecutionMode <-> bits(7) = {
  CapPtrMode <-> 0b0001001,
  IntPtrMode <-> 0b0001010,
}

mapping clause encdec = YMODESW(mode)                                               if cheri_registers_enabled()
  <-> execution_mode_funct7(mode) @ 0b00000 @ 0b00000 @ 0b001 @ 0b00000 @ 0b0110011 if cheri_registers_enabled()

mapping execution_mode_mnemonic : ExecutionMode <-> string = {
  CapPtrMode <-> "y",
  IntPtrMode <-> "i",
}

mapping clause assembly = YMODESW(mode) <-> "ymodesw." ^ execution_mode_mnemonic(mode)

/* Two arg */

mapping clause encdec = YMODER(rd, cs1)                                          if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00011 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YTYPER(rd, cs1)                                          if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00010 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YPERMR(rd, cs1)                                          if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00001 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YBASER(rd, cs1)                                          if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00101 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YLENR(rd, cs1)                                           if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00110 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YTAGR(rd, cs1)                                           if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00000 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YHIR(rd, cs1)                                            if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00100 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = YMV(cd, cs1)                                             if cheri_registers_enabled()
  <-> 0b0000110 @ 0b00000 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YSENTRY(cd, cs1)                                         if cheri_registers_enabled()
  <-> 0b0001000 @ 0b01000 @ encdec_reg(cs1) @ 0b000 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = YAMASK(rd, rs1)                                          if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00111 @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()

mapping clause assembly = YMODER(rd, cs1)  <-> "ymoder"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YTYPER(rd, cs1)  <-> "ytyper"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YPERMR(rd, cs1)  <-> "ypermr"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YBASER(rd, cs1)  <-> "ybaser"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YLENR(rd, cs1)   <-> "ylenr"   ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YTAGR(rd, cs1)   <-> "ytagr"   ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YHIR(rd, cs1)    <-> "yhir"    ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = YMV(cd, cs1)     <-> "ymv"     ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = YSENTRY(cd, cs1) <-> "ysentry" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = YAMASK(rd, rs1)  <-> "yamask"  ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)

/* Three arg */

mapping clause encdec = YPERMC(cd, cs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b010 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YMODEW(cd, cs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b111 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YADDRW(cd, cs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b001 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YHIW(cd, cs1, rs2)                                               if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b011 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = ADDY(cd, cs1, rs2)                                               if cheri_registers_enabled() & (rs2 != zreg)
  <-> 0b0000110 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b000 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled() & (rs2 != zreg)
mapping clause encdec = YBNDSRW(cd, cs1, rs2)                                            if cheri_registers_enabled()
  <-> 0b0000111 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b001 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YBNDSW(cd, cs1, rs2)                                             if cheri_registers_enabled()
  <-> 0b0000111 @ encdec_reg(rs2) @ encdec_reg(cs1) @ 0b000 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YBLD(cd, cs1, cs2)                                               if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(cs2) @ encdec_reg(cs1) @ 0b101 @ encdec_reg(cd) @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = SYEQ(rd, cs1, cs2)                                               if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(cs2) @ encdec_reg(cs1) @ 0b100 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = YLT(rd, cs1, cs2)                                                if cheri_registers_enabled()
  <-> 0b0000110 @ encdec_reg(cs2) @ encdec_reg(cs1) @ 0b110 @ encdec_reg(rd) @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = ADDIY(cd, cs1, imm12)                                 if cheri_registers_enabled()
  <-> imm12 : bits(12) @ encdec_reg(cs1) @ 0b010 @ encdec_reg(cd) @ 0b0011011 if cheri_registers_enabled()
mapping clause encdec = YBNDSIW(cd, cs1, s, uimm5)                                                    if cheri_registers_enabled() & not(s == 0b1 & uimm5 <=_u 0b00001)
  <-> 0b000001 @ s : bits(1) @ uimm5 : bits(5) @ encdec_reg(cs1) @ 0b101 @ encdec_reg(cd) @ 0b0010011 if cheri_registers_enabled() & not(s == 0b1 & uimm5 <=_u 0b00001)

mapping clause assembly = YPERMC(cd, cs1, rs2)  <-> "ypermc"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YMODEW(cd, cs1, rs2)  <-> "ymodew"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YADDRW(cd, cs1, rs2)  <-> "yaddrw"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YHIW(cd, cs1, rs2)    <-> "yhiw"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = ADDY(cd, cs1, rs2)    <-> "addy"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBNDSRW(cd, cs1, rs2) <-> "ybndsrw" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBNDSW(cd, cs1, rs2)  <-> "ybndsw"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = YBLD(cd, cs1, cs2)    <-> "ybld"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = SYEQ(rd, cs1, cs2)    <-> "syeq"    ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = YLT(rd, cs1, cs2)     <-> "ylt"     ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = ADDIY(cd, cs1, imm12) <-> "addiy"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = YBNDSIW(cd, cs1, 0b0, uimm5) <-> "ybndsiw" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(0b0000000 @ uimm5)
mapping clause assembly = YBNDSIW(cd, cs1, 0b1, uimm5) <-> "ybndsiw" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(0b000 @ uimm5 @ 0b0000)

/* Loads and stores */

let haveRV128 = xlen >= 128
let haveRV64  = xlen >= 64

mapping clause encdec = LoadCapImm(cd, rs1, offset)                 if cheri_registers_enabled()  /* ly */
  <-> offset @ encdec_reg(rs1) @ 0b100 @ encdec_reg(cd) @ 0b0001111 if cheri_registers_enabled()

mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5)                                    if cheri_registers_enabled()
  <-> off7 : bits(7) @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b100 @ off5 : bits(5) @ 0b0100011 if cheri_registers_enabled() /* sy */

mapping clause assembly = LoadCapImm(cd, rs1, offset)   <-> "ly" ^ spc() ^ cap_reg_name(cd)  ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(cs2, rs1, offset) <-> "sy" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

mapping clause encdec = LoadResCap(cd, rs1, aq, rl)                                                            if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc)
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ encdec_reg(rs1) @ 0b100 @ encdec_reg(cd) @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) /* lr.y */

mapping clause encdec = StoreCondCap(rd, cs2, rs1, aq, rl)                                                             if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc)
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b100 @ encdec_reg(rd) @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) /* sc.y */

mapping clause encdec = AMOSwapCap(cd, cs2, rs1, aq, rl)                                                               if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo)
  <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ encdec_reg(cs2) @ encdec_reg(rs1) @ 0b100 @ encdec_reg(cd) @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) /* amoswap.y */

mapping clause assembly = LoadResCap(cd, rs1, aq, rl)        <-> "lr.y"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = StoreCondCap(rd, cs2, rs1, aq, rl) <-> "sc.y"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)
mapping clause assembly = AMOSwapCap(cd, cs2, rs1, aq, rl)   <-> "amoswap.y" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)

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
mapping clause encdec_capmode = AUIPC_capmode(imm, cd)
  <-> imm @ encdec_reg(cd) @ 0b0010111
mapping clause assembly = AUIPC_capmode(imm, cd)
  <-> "auipc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_20(imm)
mapping clause encdec_capmode = JALR_capmode(imm, cs1, cd)
  <-> imm @ encdec_reg(cs1) @ 0b000 @ encdec_reg(cd) @ 0b1100111
mapping clause assembly = JALR_capmode(imm, cs1, cd)
  <-> "jalr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm)
/* See `mapping clause encdec = RISCV_JAL` for why we have to use this syntax */
mapping clause encdec_capmode = JAL_capmode(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, cd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ encdec_reg(cd) @ 0b1101111
mapping clause assembly = JAL_capmode(imm, cd)
  <-> "jal" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_21(imm)

mapping clause encdec_capmode = BEQ_reserved_capmode(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1)                                 if encdec_reg(rs1) >=_u encdec_reg(rs2)
  <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011 if encdec_reg(rs1) >=_u encdec_reg(rs2)
mapping clause assembly = BEQ_reserved_capmode (imm, rs1, rs2)
  <-> "reserved (beq" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_13(imm) ^ ")"
mapping clause encdec_capmode = BNE_reserved_capmode(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1)                                 if encdec_reg(rs1) >=_u encdec_reg(rs2)
  <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b001 @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011 if encdec_reg(rs1) >=_u encdec_reg(rs2)
mapping clause assembly = BNE_reserved_capmode (imm, rs1, rs2)
  <-> "reserved (bne" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_signed_13(imm) ^ ")"
