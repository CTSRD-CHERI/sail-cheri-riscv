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
  C(cd) = clearTagIf(newCap, not(representable));
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
  if not(validAddr(newPC) | capBoundsInfinite(PCC)) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(PCC, newPC, min_instruction_bytes())) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(newPC, E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    C(cd) = sealCap(linkCap);
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
  let cs1_val = C(cs1);

  // Calculate new PC which may be offset from the capability address.
  let off : xlenbits = sign_extend(imm);
  let newPC = [cs1_val.address + off with 0 = bitzero]; /* clear bit zero as for RISCV JALR */

  if not(capTaggedAndReservedValid(cs1_val)) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(cs1_val) & imm != zeros() then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canX(cs1_val)) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddr(newPC) | capBoundsInfinite(cs1_val)) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newPC, min_instruction_bytes())) then {
    handle_cheri_exception(CapCheckType_JBr, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if newPC[1] == bitone & not(extensionEnabled(Ext_Zca)) then {
    handle_mem_exception(newPC, E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(capIsSealed(linkCap)), "Link cap should always be unsealed");
    C(cd) = sealCap(linkCap);
    set_next_pc(newPC);

    // Construct the new capability pointing to the address + offset.
    let (representable, newPCC) = setCapAddr(cs1_val, newPC);
    assert(representable, "If bounds checks passed then new PCC must be representable");
    set_next_pcc(unsealCap(newPCC));

    RETIRE_SUCCESS
  }
}

/* Operations that extract parts of a capability into GPR */

union clause ast = GCPERM : (regidx, regidx)
union clause ast = GCBASE : (regidx, regidx)
union clause ast = GCLEN  : (regidx, regidx)
union clause ast = GCTAG  : (regidx, regidx)
union clause ast = GCHI   : (regidx, regidx)
union clause ast = GCMODE : (regidx, regidx)
union clause ast = GCTYPE : (regidx, regidx)

/*!
 * insnref: gcmode_32bit brief
 * Capability get CHERI execution mode
 *
 * gcmode rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (GCMODE(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = zero_extend(execution_mode_encdec(getCapMode(capVal)));
  RETIRE_SUCCESS
}

/*!
 * insnref: gctype_32bit brief
 * Capability get type
 *
 * gctype rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (GCTYPE(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = zero_extend(bool_to_bits(capVal.sealed));
  RETIRE_SUCCESS
}

/*!
 * insnref: gcperm_32bit brief
 * Capability get permissions
 *
 * gcperm rd, cs1
 *
 * See ISA document for full description
 */
function clause execute (GCPERM(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = packPerms(getArchPermsLegalized(capVal), capVal.sd_perms).bits;
  RETIRE_SUCCESS
}

/*!
 * insnref: gcbase_32bit
 * Capability get base address
 *
 * gcbase rd, cs1
 *
 * Decode the base integer address from cs1's bounds and write the result
 * to rd. It is not required that the input capability cs1  has its tag
 * set to 1.
 */

function clause execute (GCBASE(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = match getCapBoundsBits(capVal) {
    None() => zeros(),
    Some(base, _) => base
  };
  RETIRE_SUCCESS
}

/*!
 * insnref: gchi_32bit
 * Capability get metadata
 *
 * gchi rd, cs1
 *
 * Copy the metadata (bits [CLEN-1:MXLEN]) of capability cs1 into rd.
 */
function clause execute (GCHI(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = capToMetadataBits(capVal).bits;
  RETIRE_SUCCESS
}

union clause ast = SCHI : (regidx, regidx, regidx)
/*!
 * insnref: schi_32bit
 * Capability set metadata
 *
 * schi cd, cs1, rs2
 *
 * Copy cs1  to cd , replace the capability metadata (i.e. bits
 * [CLEN-1:MXLEN]) with rs2  and set cd.tag to 0.
 */
function clause execute (SCHI(cd, cs1, rs2)) = {
  let capVal = C(cs1);
  let intVal = X(rs2);
  let newCap = bitsToCap(false, intVal @ capVal.address);
  C(cd) = newCap;
  RETIRE_SUCCESS
}

/*!
 * insnref: gclen_32bit
 * Capability get length
 *
 * gclen rd, cs1
 *
 * Calculate the length of cs1's bounds and write the result in rd. The
 * length is defined as the difference between the decoded bounds' top
 * and base addresses i.e. top - base. It is not required that the input
 * capability cs1  has its tag set to 1. GCLEN outputs 0 if cs1's bounds
 * are malformed (see Malformed Capability Bounds), and 2^MXLEN^-1 if the
 * length of cs1 is 2^MXLEN^.
 */
function clause execute (GCLEN(rd, cs1)) = {
  let capVal = C(cs1);
  // getCapLength returns 0 if the bounds are malformed
  let len = getCapLength(capVal);
  X(rd) = to_bits(xlen, if len > cap_max_addr then cap_max_addr else len);
  RETIRE_SUCCESS
}

/*!
 * insnref: gctag_32bit
 * Capability get tag
 *
 * gctag rd, cs1
 *
 * Zero extend the value of cs1.tag and write the result to rd.
 */
function clause execute (GCTAG(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = zero_extend(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

union clause ast = ACPERM : (regidx, regidx, regidx)
/*!
 * insnref: acperm_32bit brief
 * Mask capability permissions
 *
 * acperm cd, cs1, rs2
 *
 * See ISA document for full description
 */
function clause execute(ACPERM(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let cond = capIsSealed(cs1_val) | not(capReservedValid(cs1_val));
  let inCap = clearTagIf(cs1_val, cond);

  let old_perms = packPerms(getArchPermsLegalized(inCap), inCap.sd_perms).bits;

  let new_perms = old_perms & rs2_val;

  let (new_arch_perms, new_sd_perms) = unpackPerms(struct {bits = new_perms});
  let newCap = { setArchPerms(inCap, new_arch_perms) with sd_perms = new_sd_perms };

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = SCMODE : (regidx, regidx, regidx)
/*!
 * insnref: scmode_32bit
 * Capability set CHERI execution mode
 *
 * scmode cd, cs1, rs2
 *
 * Copy cs1 to cd. Clear cd.tag if cs1 is sealed. Update the M-bit of cd
 * to the least significant bit of rs2 if the two following conditions
 * are met, otherwise do not update it:
 * . X-permission is set
 * . The existing permissions can be produced by ACPERM
 */
function clause execute(SCMODE(cd, cs1, rs2)) = {
  let cap = C(cs1);
  let mode = execution_mode_encdec(X(rs2)[0 .. 0]);

  let cap = clearTagIf(cap, capIsSealed(cap));
  let hasMode = not(permsMalformed(cap)) & canX(cap);
  let newCap = if hasMode then setCapMode(cap, mode) else cap;

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = MODESW : unit
/*!
 * insnref: modesw_32bit
 * Switch CHERI execution mode
 *
 * modesw
 *
 * Toggle the hart's current CHERI execution mode in pcc.
 *
 * * If the current mode in pcc is _Integer Pointer Mode_ (1), then the
 * M-bit in pcc is set to _Capability Pointer Mode_ (0).
 * * If the current mode is _Capability Pointer Mode_ (0), then the M-bit
 * in pcc is set to _Integer Pointer Mode_ (1).
 *
 * Executing MODESW from the program buffer in debug mode updates the M-bit
 * of dinfc. The M-bit of dinfc sets the CHERI execution mode for the
 * execution of the next instruction from the program buffer, and is used
 * to control which CHERI execution mode to enter next time debug mode is entered.
 * The CHERI execution mode is only controlled by the M-bit of dinfc in debug mode.
 */
function clause execute(MODESW()) = {
  let mode : ExecutionMode = match effective_cheri_mode() {
    IntPtrMode => CapPtrMode,
    CapPtrMode => IntPtrMode,
  };
  if debug_mode_active then dinfc = setCapMode(infinite_cap, mode);
  set_next_pcc(setCapMode(PCC, mode));
  RETIRE_SUCCESS
}

union clause ast = CADD : (regidx, regidx, regidx)
/*!
 * insnref: cadd_32bit
 * Capability pointer increment
 *
 * cadd cd, cs1, rs2
 * caddi cd, cs1, imm
 *
 * Increment the address field of the capability cs1  and write the
 * result to cd . The tag bit of the output capability is 0 if cs1  did
 * not have its tag set to 1, the incremented address is outside cs1's
 * Representable Range or cs1  is sealed.
 *
 * For CADD, the address is incremented by the value in rs2 .
 * For CADDI, the address is incremented by the immediate value imm.
 */
function clause execute (CADD(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let newCap = incCapAddrChecked(cs1_val, rs2_val);

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = CADDI : (regidx, regidx, bits(12))
/*!
 * insnref: cadd_32bit
 * Capability pointer increment
 *
 * cadd cd, cs1, rs2
 * caddi cd, cs1, imm
 *
 * Increment the address field of the capability cs1  and write the
 * result to cd . The tag bit of the output capability is 0 if cs1  did
 * not have its tag set to 1, the incremented address is outside cs1's
 * Representable Range or cs1  is sealed.
 *
 * For CADD, the address is incremented by the value in rs2 .
 * For CADDI, the address is incremented by the immediate value imm.
 */
function clause execute (CADDI(cd, cs1, imm)) = {
  let cs1_val = C(cs1);
  let immBits : xlenbits = sign_extend(imm);

  let newCap = incCapAddrChecked(cs1_val, immBits);

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = SCADDR : (regidx, regidx, regidx)
/*!
 * insnref: scaddr_32bit
 * Capability set address
 *
 * scaddr cd, cs1, rs2
 *
 * Set the address field of capability cs1 to rs2 and write the output
 * capability to cd. The tag bit of the output capability is 0 if cs1 did
 * not have its tag set to 1, rs2 is outside the Representable Range of
 * cs1 or if cs1 is sealed.
 */
function clause execute (SCADDR(cd, cs1, rs2)) = {
  C(cd) = setCapAddrChecked(C(cs1), X(rs2));
  RETIRE_SUCCESS
}

union clause ast = SCBNDSR : (regidx, regidx, regidx)
/*!
 * insnref: scbndsr_32bit
 * Capability set bounds, rounding up if necessary
 *
 * scbndsr cd, cs1, rs2
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address
 * field and the length of its bounds set to rs2. The base is rounded
 * down and the length is rounded up by the smallest amount needed to
 * form a representable capability covering the requested bounds. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0 or cs1  is sealed.
 */
function clause execute (SCBNDSR(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let length = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (_, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  let cond = not(inBounds) |
             boundsMalformed(newCap) |
             not(capReservedValid(newCap)) |
             capIsSealed(newCap);
  C(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = SCBNDSI : (regidx, regidx, bits(1), bits(5))
/*!
 * insnref: scbnds_32bit
 * Capability set bounds
 *
 * scbnds cd, cs1, rs2
 * scbndsi cd, cs1, uimm
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set cd.tag to 0. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0  or cs1 is sealed.
 * SCBNDSI uses the s bit to scale the immediate by 4 places
 * immediate = ZeroExtend(s ? uimm<<4 : uimm)
 */
function clause execute (SCBNDSI(cd, cs1, s, uimm5)) = {
  let cs1_val = C(cs1);
  let length = if s == 0b1 then uimm5 @ 0b0000 else 0b0000 @ uimm5;
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  assert(exact, "SCBNDSI immediate too small for non-exact lengths");
  let cond = not(inBounds) |
             boundsMalformed(newCap) |
             not(capReservedValid(newCap)) |
             capIsSealed(newCap);
  C(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = SCBNDS : (regidx, regidx, regidx)
/*!
 * insnref: scbnds_32bit
 * Capability set bounds
 *
 * scbnds cd, cs1, rs2
 * scbndsi cd, cs1, uimm
 *
 * Capability register cd  is set to capability register cs1  with the
 * base address of its bounds replaced with the value of cs1.address and
 * the length of its bounds set to rs2  (or imm). If the resulting
 * capability cannot be represented exactly then set cd.tag to 0. In all
 * cases, cd.tag is set to 0 if its bounds exceed cs1's bounds, cs1's tag
 * is 0  or cs1 is sealed.
 * SCBNDSI uses the s bit to scale the immediate by 4 places
 * immediate = ZeroExtend(s ? uimm<<4 : uimm)
 */
function clause execute (SCBNDS(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let length = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = zero_extend(newBase) + zero_extend(length);
  // inCapBoundsNoWrap returns false if the input bounds are malformed.
  let inBounds = inCapBoundsNoWrap(cs1_val, newBase, unsigned(length));
  let (exact, newCap) : (bool, Capability) = setCapBounds(cs1_val, newBase, newTop);
  let cond = not(inBounds & exact) |
             boundsMalformed(newCap) |
             not(capReservedValid(newCap)) |
             capIsSealed(newCap);
  C(cd) = clearTagIf(newCap, cond);
  RETIRE_SUCCESS
}

union clause ast = CMV : (regidx, regidx)
/*!
 * insnref: cmv_32bit
 * Capability move
 *
 * cmv cd, cs1
 *
 * The contents of capability register cs1  are written to capability
 * register cd. CMV unconditionally moves the whole capability to cd .
 */
function clause execute (CMV(cd, cs1)) = {
  C(cd) = C(cs1);
  RETIRE_SUCCESS
}

union clause ast = CBLD : (regidx, regidx, regidx)
/*!
 * insnref: cbld_32bit
 * Capability build
 *
 * cbld cd, cs1, cs2
 *
 * Copy cs2 to cd and set cd.tag to 1 if
 *
 * . cs1.tag is set, and
 * . cs1's bounds are not malformed, and all reserved fields are zero,
 * and
 * . cs1's permissions could have been legally produced by ACPERM, and
 * . cs1 is not sealed, and
 * . cs2's permissions and bounds are equal to or a subset of cs1's, and
 * . cs2's bounds are not malformed, and all reserved fields are zero,
 * and
 * . cs2's permissions could have been legally produced by ACPERM, and
 * . All reserved bits in cs2's metadata are 0;
 * Otherwise, copy cs2 to cd and clear cd's tag.
 * CBLD is typically used alongside SCHI to build capabilities from
 * integer values.
 */
function clause execute (CBLD(cd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);

  let tag = cs1_val.tag &
            not(capIsSealed(cs1_val)) &
            capIsSubset(cs2_val, cs1_val); /* Subset checks for malformed bounds,
                                              perms, and reserved bits */

  C(cd) = { cs2_val with tag = tag };
  RETIRE_SUCCESS
}

union clause ast = CRAM : (regidx, regidx)
/*!
 * insnref: cram_32bit
 * Get Capability Representable Alignment Mask (CRAM)
 *
 * cram rd, rs1
 *
 * Integer register rd is set to a mask that can be used to round
 * addresses down to a value that is sufficiently aligned to set exact
 * bounds for the nearest representable length of rs1.
 */
function clause execute(CRAM(rd, rs1)) = {
  let len = X(rs1);
  X(rd) = getRepresentableAlignmentMask(len);
  RETIRE_SUCCESS
}

union clause ast = SCSS : (regidx, regidx, regidx)
/*!
 * insnref: scss_32bit
 * Capability test subset
 *
 * scss rd, cs1, cs2
 *
 * rd is set to 1 if the tag of capabilities cs1 and cs2 are equal and
 * the bounds and permissions of cs2 are a subset of those of cs1.
 * If either cs1 or cs2:
 *
 * . Have bounds which are malformed, or
 * . Have any bits set in reserved fields, or
 * . Have permissions that could not have been legally produced by ACPERM
 * then the instruction returns zero.
 */
function clause execute (SCSS(rd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);

  X(rd) = zero_extend(bool_bits(
    (cs1_val.tag == cs2_val.tag) &
    capIsSubset(cs2_val, cs1_val) /* capIsSubset returns false if either input
                                     has malformed bounds, perms, or non-zero
                                     reserved bits */
  ));
  RETIRE_SUCCESS
}

union clause ast = SCEQ : (regidx, regidx, regidx)
/*!
 * insnref: sceq_32bit
 * Set if Capabilities are EQual
 *
 * sceq rd, cs1, cs2
 *
 * rd is set to 1 if all bits (i.e. CLEN bits and the tag) of
 * capabilities cs1 and cs2  are equal, otherwise rd is set to 0.
 */
function clause execute (SCEQ(rd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  X(rd) = zero_extend(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

union clause ast = SENTRY : (regidx, regidx)
/*!
 * insnref: sentry_32bit
 * Seal capability as sealed entry.
 *
 * sentry cd, cs1
 *
 * Capability `cd` is written with the capability in `cs1` with its type bit set to 1.
 * Attempting to seal an already sealed capability will lead to the tag of `cd` being set to 0.
 */
function clause execute (SENTRY(cd, cs1)) = {
  let cs1_val = C(cs1);
  let inCap = clearTagIf(cs1_val, capIsSealed(cs1_val));
  C(cd) = sealCap(inCap);
  RETIRE_SUCCESS
}

union clause ast = LoadResCap : (regidx, regidx, bool, bool)
/*
 * insnref: load_res_cap_32bit modedep
 * Load Reserved Capability (LR.C), 32-bit encodings
 *
 * Capability Pointer Mode:
 * lr.c cd, 0(cs1)
 *
 * Integer Pointer Mode:
 * lr.c cd, 0(rs1)
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

  match check_and_handle_load_vaddr_for_triggers(vaddr, get_arch_pc()) {
    Some (ret) => return ret,
    None () => ()
  };
  if not(capTaggedAndReservedValid(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(auth_val) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canR(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddr, cap_size)) then {
    handle_mem_exception(vaddr, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddr, Read(Cap)) {
    TR_Failure(E_Extension(_)) => { internal_error(__FILE__, __LINE__, "unexpected cheri exception for cap load") },
    TR_Failure(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
    TR_Address(addr, pbmt, ptw_info) => {
      let c = mem_read_cap(addr, pbmt, aq, aq & rl, false);
      match c {
        MemValue(v) => {
          let cr = if ptw_info.ptw_lc == PTW_LC_CLEAR
                   then clearTag(v) /* strip the tag */
                   else {
                     /* the Sail model currently reserves physical addresses */
                     load_reservation(addr);
                     clearTagIf(v, not(canC(auth_val)))
                   };
          C(cd) = legalizeLM(cr, auth_val);
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddr, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = LoadCapImm : (regidx, regidx, bits(12))
/*!
 * insnref: load_32bit_cap modedep
 * Load capability
 *
 * Capability Pointer Mode:
 * lc cd, offset(cs1)
 *
 * Integer Pointer Mode:
 * lc cd, offset(rs1)
 *
 * Capability Pointer Mode:
 * Load a CLEN+1 bit value from memory and writes it to cd. The
 * capability in cs1 authorizes the operation. The effective address of
 * the memory access is obtained by adding the address of cs1 to the
 * sign-extended 12-bit offset. The tag value written to cd is 0 if the
 * tag of the memory location loaded is 0 or cs1 does not grant
 * C-permission.
 *
 * Integer Pointer Mode:
 * Loads a CLEN+1 bit value from memory and writes it to cd. The
 * capability authorising the operation is ddc. The effective address of
 * the memory access is obtained by adding rs1 to the sign-extended
 * 12-bit offset. The tag value written to cd is 0 if the tag of the
 * memory location loaded is 0 or ddc does not grant C-permission.
 */
function clause execute LoadCapImm(cd, rs1_cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, offset);
  let aq : bool = false;
  let rl : bool = false;

  match check_and_handle_load_vaddr_for_triggers(vaddr, get_arch_pc()) {
    Some (ret) => return ret,
    None () => ()
  };
  if not(capTaggedAndReservedValid(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(auth_val) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canR(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddr, cap_size)) then {
    handle_mem_exception(vaddr, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddr, Read(Cap)) {
    TR_Failure(E_Extension(_)) => { internal_error(__FILE__, __LINE__, "unexpected cheri exception for cap load") },
    TR_Failure(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
    TR_Address(addr, pbmt, ptw_info) => {
      let c = mem_read_cap(addr, pbmt, aq, aq & rl, false);
      match c {
        MemValue(v) => {
          let cr = clearTagIf(v, ptw_info.ptw_lc == PTW_LC_CLEAR | not(canC(auth_val)));
          C(cd) = legalizeLM(cr, auth_val);
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddr, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = StoreCapImm : (regidx, regidx, bits(12))
/*!
 * insnref: store_32bit_cap modedep
 * Store capability
 *
 * Capability Pointer Mode:
 * sc cs2, offset(cs1)
 *
 * Integer Pointer Mode:
 * sc cs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Store the CLEN+1 bit value in cs2 to memory. The capability in cs1
 * authorizes the operation. The effective address of the memory access
 * is obtained by adding the address of cs1 to the sign-extended 12-bit
 * offset. The capability written to memory has the tag set to 0 if the
 * tag of cs2 is 0 or cs1 does not grant C-permission.
 *
 * Integer Pointer Mode:
 * Store the CLEN+1 bit value in cs2 to memory. The capability
 * authorising the operation is ddc. The effective address of the memory
 * access is obtained by adding rs1 to the sign-extended 12-bit offset.
 * The capability written to memory has the tag set to 0 if cs2's tag is
 * 0 or ddc does not grant C-permission.
 */
function clause execute StoreCapImm(cs2, rs1_cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, offset);
  let cs2_val = C(cs2);
  let aq : bool = false;
  let rl : bool = false;
  let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));

  match check_and_handle_store_vaddr_for_triggers(vaddr, get_arch_pc()) {
    Some (ret) => return ret,
    None () => ()
  };
  if not(capTaggedAndReservedValid(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(auth_val) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canW(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddr, cap_size)) then {
    handle_mem_exception(vaddr, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddr, Write(if cs2_val.tag then Cap else Data)) {
    TR_Failure(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
    TR_Address(addr, pbmt, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        MemValue(_) => {
          let res : MemoryOpResult(bool) = mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false);
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

union clause ast = StoreCondCap : (regidx, regidx, regidx, bool, bool)
/*!
 * insnref: store_cond_cap_32bit modedep
 * Store Conditional (SC.C), 32-bit encoding
 *
 * Capability Pointer Mode:
 * sc.c rd, cs2, 0(cs1)
 *
 * Integer Pointer Mode:
 * sc.c rd, cs2, 0(rs1)
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
  let cs2_val = C(cs2);
  let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));

  match check_and_handle_store_vaddr_for_triggers(vaddr, get_arch_pc()) {
    Some (ret) => return ret,
    None () => ()
  };
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    X(rd) = zero_extend(0b1);
    return RETIRE_SUCCESS
  };
  if not(capTaggedAndReservedValid(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(auth_val) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canW(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddr, cap_size)) then {
    handle_mem_exception(vaddr, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else {
    match translateAddr(vaddr, Write(if cs2_val.tag then Cap else Data)) {
      TR_Failure(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
      TR_Address(addr, pbmt, _) => {
        if not(match_reservation(addr)) then {
          /* cannot happen in rmem */
          X(rd) = zero_extend(0b1);
          cancel_reservation();
          RETIRE_SUCCESS
        } else {
          let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
          match (eares) {
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            MemValue(_) => {
              let res : MemoryOpResult(bool) = mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false);
              match (res) {
                MemValue(true)  => {
                  X(rd) = zero_extend(0b0);
                  cancel_reservation();
                  RETIRE_SUCCESS
                },
                MemValue(false) => {
                  X(rd) = zero_extend(0b1);
                  cancel_reservation();
                  RETIRE_SUCCESS
                },
                MemException(e) => {
                  handle_mem_exception(vaddr, e);
                  RETIRE_FAIL
                }
              }
            }
          }
        }
      }
    }
  }
}

union clause ast = AMOSwapCap : (regidx, regidx, regidx, bool, bool)
/*!
 * insnref: amoswap_32bit_cap modedep
 * Atomic Operation (AMOSWAP.C), 32-bit encoding
 *
 * Capability Pointer Mode:
 * amoswap.c cd, cs2, offset(cs1)
 *
 * Integer Pointer Mode:
 * amoswap.c cd, cs2, offset(rs1)
 *
 * Capability Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in cs1.
 *
 * Integer Pointer Mode:
 * Atomic swap of capability type, authorised by the capability in ddc.
 */
function clause execute AMOSwapCap(cd, cs2, rs1_cs1, aq, rl) = {
  let (auth_val, vaddr) = get_cheri_mode_cap_addr(rs1_cs1, zeros());
  let cs2_val = C(cs2);
  let cs2_val = clearTagIf(cs2_val, not(canC(auth_val)));

  match check_and_handle_amo_vaddr_for_triggers(vaddr, get_arch_pc()) {
    Some (ret) => return ret,
    None () => ()
  };
  if not(capTaggedAndReservedValid(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_TagViolation);
    RETIRE_FAIL
  } else if capIsSealed(auth_val) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_SealViolation);
    RETIRE_FAIL
  } else if not(canR(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(canW(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_PermissionViolation);
    RETIRE_FAIL
  } else if not(validAddrRange(vaddr, cap_size) | capBoundsInfinite(auth_val)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_InvalidAddressViolation);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
    handle_cheri_exception(CapCheckType_Data, CapEx_LengthViolation);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddr, cap_size)) then {
    handle_mem_exception(vaddr, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else {
    match translateAddr(vaddr, ReadWrite(Cap, if cs2_val.tag then Cap else Data)) {
      TR_Failure(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
      TR_Address(addr, pbmt, ptw_info) => {
        let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
        match (eares) {
          MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
          MemValue(_) => {
            let c = mem_read_cap(addr, pbmt, aq, aq & rl, false);
            match c {
              MemValue(v) => {
                let wres : MemoryOpResult(bool) = mem_write_cap(addr, pbmt, cs2_val, aq & rl, rl, false);
                match wres {
                  MemValue(_) => {
                    let cr = clearTagIf(v, ptw_info.ptw_lc == PTW_LC_CLEAR | not(canC(auth_val)));
                    C(cd) = legalizeLM(cr, auth_val);
                    RETIRE_SUCCESS
                  },
                  MemException(e) => {
                    handle_mem_exception(vaddr, e);
                    RETIRE_FAIL
                  }
                }
              },
              MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
            }
          }
        }
      }
    }
  }
}

/* Zero arg */

mapping clause encdec = MODESW()                                  if cheri_registers_enabled()
  <-> 0b0001001 @ 0b00000 @ 0b00000 @ 0b001 @ 0b00000 @ 0b0110011 if cheri_registers_enabled()

mapping clause assembly = MODESW() <-> "modesw"

/* Two arg */

mapping clause encdec = GCMODE(rd, cs1)                  if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00011 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCTYPE(rd, cs1)                  if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00010 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCPERM(rd, cs1)                  if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00001 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCBASE(rd, cs1)                  if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00101 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCLEN(rd, cs1)                   if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00110 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCTAG(rd, cs1)                   if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00000 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = GCHI(rd, cs1)                    if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00100 @ cs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = CMV(cd, cs1)                     if cheri_registers_enabled()
  <-> 0b0000110 @ 0b00000 @ cs1 @ 0b000 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SENTRY(cd, cs1)                  if cheri_registers_enabled()
  <-> 0b0001000 @ 0b01000 @ cs1 @ 0b000 @ cd @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = CRAM(rd, rs1)                    if cheri_registers_enabled()
  <-> 0b0001000 @ 0b00111 @ rs1 @ 0b000 @ rd @ 0b0110011 if cheri_registers_enabled()

mapping clause assembly = GCMODE(rd, cs1) <-> "gcmode" ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCTYPE(rd, cs1) <-> "gctype" ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCPERM(rd, cs1) <-> "gcperm" ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCBASE(rd, cs1) <-> "gcbase" ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCLEN(rd, cs1)  <-> "gclen"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCTAG(rd, cs1)  <-> "gctag"  ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = GCHI(rd, cs1)   <-> "gchi"   ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CMV(cd, cs1)    <-> "cmv"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = SENTRY(cd, cs1) <-> "sentry" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CRAM(rd, rs1)   <-> "cram"   ^ spc() ^ reg_name(rd)     ^ sep() ^ reg_name(rs1)

/* Three arg */

mapping clause encdec = ACPERM(cd, cs1, rs2)         if cheri_registers_enabled()
  <-> 0b0000110 @ rs2 @ cs1 @ 0b010 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SCMODE(cd, cs1, rs2)         if cheri_registers_enabled()
  <-> 0b0000110 @ rs2 @ cs1 @ 0b111 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SCADDR(cd, cs1, rs2)         if cheri_registers_enabled()
  <-> 0b0000110 @ rs2 @ cs1 @ 0b001 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SCHI(cd, cs1, rs2)           if cheri_registers_enabled()
  <-> 0b0000110 @ rs2 @ cs1 @ 0b011 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = CADD(cd, cs1, rs2)           if cheri_registers_enabled() & (rs2 != zreg)
  <-> 0b0000110 @ rs2 @ cs1 @ 0b000 @ cd @ 0b0110011 if cheri_registers_enabled() & (rs2 != zreg)
mapping clause encdec = SCBNDSR(cd, cs1, rs2)        if cheri_registers_enabled()
  <-> 0b0000111 @ rs2 @ cs1 @ 0b001 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SCBNDS(cd, cs1, rs2)         if cheri_registers_enabled()
  <-> 0b0000111 @ rs2 @ cs1 @ 0b000 @ cd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = CBLD(cd, cs1, cs2)           if cheri_registers_enabled()
  <-> 0b0000110 @ cs2 @ cs1 @ 0b101 @ cd @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = SCEQ(rd, cs1, cs2)           if cheri_registers_enabled()
  <-> 0b0000110 @ cs2 @ cs1 @ 0b100 @ rd @ 0b0110011 if cheri_registers_enabled()
mapping clause encdec = SCSS(rd, cs1, cs2)           if cheri_registers_enabled()
  <-> 0b0000110 @ cs2 @ cs1 @ 0b110 @ rd @ 0b0110011 if cheri_registers_enabled()

mapping clause encdec = CADDI(cd, cs1, imm12)         if cheri_registers_enabled()
  <-> imm12 : bits(12) @ cs1 @ 0b010 @ cd @ 0b0011011 if cheri_registers_enabled()
mapping clause encdec = SCBNDSI(cd, cs1, s, uimm5)                            if cheri_registers_enabled()
  <-> 0b000001 @ s : bits(1) @ uimm5 : bits(5) @ cs1 @ 0b101 @ cd @ 0b0010011 if cheri_registers_enabled()

mapping clause assembly = ACPERM(cd, cs1, rs2)  <-> "acperm"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = SCMODE(cd, cs1, rs2)  <-> "scmode"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = SCADDR(cd, cs1, rs2)  <-> "scaddr"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = SCHI(cd, cs1, rs2)    <-> "schi"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CADD(cd, cs1, rs2)    <-> "cadd"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = SCBNDSR(cd, cs1, rs2) <-> "scbndsr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = SCBNDS(cd, cs1, rs2)  <-> "scbnds"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CBLD(cd, cs1, cs2)    <-> "cbld"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = SCEQ(rd, cs1, cs2)    <-> "sceq"    ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = SCSS(rd, cs1, cs2)    <-> "scss"    ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CADDI(cd, cs1, imm12) <-> "caddi"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = SCBNDSI(cd, cs1, 0b0, uimm5) <-> "scbndsi" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(0b0000000 @ uimm5)
mapping clause assembly = SCBNDSI(cd, cs1, 0b1, uimm5) <-> "scbndsi" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(0b000 @ uimm5 @ 0b0000)

/* Loads and stores */

let haveRV128 = xlen >= 128
let haveRV64  = xlen >= 64

mapping clause encdec = LoadCapImm(cd, rs1, offset) if cheri_registers_enabled() & xlen == 64  /* lc */
  <-> offset @ rs1 @ 0b100 @ cd @ 0b0001111         if cheri_registers_enabled() & xlen == 64
mapping clause encdec = LoadCapImm(cd, rs1, offset) if cheri_registers_enabled() & xlen == 32  /* lc */
  <-> offset @ rs1 @ 0b011 @ cd @ 0b0000011         if cheri_registers_enabled() & xlen == 32

mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5)            if cheri_registers_enabled() & xlen == 64
  <-> off7 : bits(7) @ cs2 @ rs1 @ 0b100 @ off5 : bits(5) @ 0b0100011 if cheri_registers_enabled() & xlen == 64 /* sc */
mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5)            if cheri_registers_enabled() & xlen == 32
  <-> off7 : bits(7) @ cs2 @ rs1 @ 0b011 @ off5 : bits(5) @ 0b0100011 if cheri_registers_enabled() & xlen == 32 /* sc */

mapping clause assembly = LoadCapImm(cd, rs1, offset)   <-> "lc" ^ spc() ^ cap_reg_name(cd)  ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(cs2, rs1, offset) <-> "sc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

mapping clause encdec = LoadResCap(cd, rs1, aq, rl)                                    if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 32
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b011 @ cd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 32 /* lr.c (RV32) */
mapping clause encdec = LoadResCap(cd, rs1, aq, rl)                                    if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 64
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b100 @ cd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 64 /* lr.c (RV64) */

mapping clause encdec = StoreCondCap(rd, cs2, rs1, aq, rl)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 32
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b011 @ rd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 32 /* sc.c (RV32) */
mapping clause encdec = StoreCondCap(rd, cs2, rs1, aq, rl)                         if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 64
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b100 @ rd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zalrsc) & xlen == 64 /* sc.c (RV64) */

mapping clause encdec = AMOSwapCap(cd, cs2, rs1, aq, rl)                           if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) & xlen == 32
  <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b011 @ cd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) & xlen == 32 /* amoswap.c (RV64) */
mapping clause encdec = AMOSwapCap(cd, cs2, rs1, aq, rl)                           if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) & xlen == 64
  <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b100 @ cd @ 0b0101111 if cheri_registers_enabled() & extensionEnabled(Ext_Zaamo) & xlen == 64 /* amoswap.c (RV64) */

mapping clause assembly = LoadResCap(cd, rs1, aq, rl)        <-> "lr.c"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = StoreCondCap(rd, cs2, rs1, aq, rl) <-> "sc.c"      ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd)     ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)
mapping clause assembly = AMOSwapCap(cd, cs2, rs1, aq, rl)   <-> "amoswap.c" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)

/*
  CHERI really needs sub word atomic operations because bounds checks mean you
  can't implement them in software with word sized operations. The RISC-V
  spec. does not define lr / sc for bytes or half words although the obvious
  encodings are vacant. Since the base Sail model actually implements the unused
  widths but refuses to decode them we can implement them for CHERI simply by
  adding the decodings here.
*/
mapping clause encdec = LOADRES(aq, rl, rs1, size, rd)                                                if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b0 @ size_enc(size) @ rd @ 0b0101111 if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
mapping clause encdec = STORECON(aq, rl, rs2, rs1, size, rd)                                      if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_enc(size) @ rd @ 0b0101111 if extensionEnabled(Ext_Zalrsc) & ((size == BYTE) | (size == HALF))

/*
 * Encoding/assembly mappings for capmode specific instructions. This does not
 * include loads/stores since they are not decoded differently, but instead
 * use hooks for semantic differences.
 */
mapping clause encdec_capmode = AUIPC_capmode(imm, cd)
  <-> imm @ cd @ 0b0010111
mapping clause assembly = AUIPC_capmode(imm, cd)
  <-> "auipc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_20(imm)
mapping clause encdec_capmode = JALR_capmode(imm, cs1, cd)
  <-> imm @ cs1 @ 0b000 @ cd @ 0b1100111
mapping clause assembly = JALR_capmode(imm, cs1, cd)
  <-> "jalr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm)
/* See `mapping clause encdec = RISCV_JAL` for why we have to use this syntax */
mapping clause encdec_capmode = JAL_capmode(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, cd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ cd @ 0b1101111
mapping clause assembly = JAL_capmode(imm, cd)
  <-> "jal" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_21(imm)
