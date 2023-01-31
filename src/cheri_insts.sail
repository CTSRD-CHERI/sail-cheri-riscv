/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* Capability versions of mode-dependent instructions */

union clause ast = AUIPCC : (bits(20), regidx)
/*!
 * Capability register *cd* is replaced with the contents of **PCC**, with the
 * **address** replaced with **PCC**.**address** $+$ *imm* $\times$ 4096.
 */
function clause execute AUIPCC(imm, cd) = {
  let off : xlenbits = EXTS(imm @ 0x000);
  let (representable, newCap) = setCapAddr(PCC, PC + off);
  C(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}

union clause ast = CJAL : (bits(21), regidx)
/*!
 * Capability register *cd* is replaced with the next instruction's **PCC** and
 * sealed as a sentry. **PCC**.**address** is incremented by *imm*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **PCC**.**address** $+$ *imm* $\lt$ **PCC**.**base**.
 *   - **PCC**.**address** $+$ *imm* $+$ min_instruction_bytes $\gt$ **PCC**.**top**.
 *   - **PCC**.**address** $+$ *imm* is unaligned, ignoring bit 0.
 */
function clause execute(CJAL(imm, cd)) = {
  let off : xlenbits = EXTS(imm);
  let newPC = PC + off;
  if not(inCapBounds(PCC, newPC, min_instruction_bytes())) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, PCC_IDX);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(isCapSealed(linkCap)), "Link cap should always be unsealed");
    C(cd) = sealCap(linkCap, to_bits(cap_otype_width, otype_sentry));
    nextPC = newPC;
    RETIRE_SUCCESS
  }
}

union clause ast = CJALR : (bits(12), regidx, regidx)
/*!
 * Capability register *cd* is replaced with the next instruction's **PCC** and
 * sealed as a sentry. **PCC** is replaced with the value of capability
 * register *cs1* with its **address** incremented by *imm* and the 0th bit of
 * its **address** set to 0, and is unsealed if it is a sentry.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed and is not a sentry.
 *   - *cs1* is a sentry and *imm* $\ne$ 0.
 *   - *cs1*.**perms** does not grant **Permit_Execute**.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ min_instruction_bytes $\gt$ *cs1*.**top**.
 *   - *cs1*.**base** is unaligned.
 *   - *cs1*.**address** $+$ *imm* is unaligned, ignoring bit 0.
 */
function clause execute(CJALR(imm, cs1, cd)) = {
  let cs1_val = C(cs1);
  let off : xlenbits = EXTS(imm);
  let newPC = [cs1_val.address + off with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cs1_val);
  if not(cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(cs1_val) &
            ((signed(cs1_val.otype) != otype_sentry) | imm != zeros()) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not(cs1_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newPC, min_instruction_bytes())) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if newPCCBase[0] == bitone | (newPCCBase[1] == bitone & ~(haveRVC())) then {
    handle_cheri_reg_exception(CapEx_UnalignedBase, cs1);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not(isCapSealed(linkCap)), "Link cap should always be unsealed");
    C(cd) = sealCap(linkCap, to_bits(cap_otype_width, otype_sentry));
    nextPC = newPC;
    nextPCC = unsealCap(cs1_val);
    RETIRE_SUCCESS
  }
}

/* Operations that extract parts of a capability into GPR */

union clause ast = CGetPerm   : (regidx, regidx)
union clause ast = CGetType   : (regidx, regidx)
union clause ast = CGetBase   : (regidx, regidx)
union clause ast = CGetLen    : (regidx, regidx)
union clause ast = CGetTag    : (regidx, regidx)
union clause ast = CGetSealed : (regidx, regidx)
union clause ast = CGetOffset : (regidx, regidx)
union clause ast = CGetAddr   : (regidx, regidx)
union clause ast = CGetFlags  : (regidx, regidx)
union clause ast = CGetHigh   : (regidx, regidx)
union clause ast = CGetTop    : (regidx, regidx)

/*!
 * The least significant [cap_hperms_width] bits of integer register *rd* are
 * set equal to the **perms** field of capability register *cs1*; bits
 * [cap_uperms_shift] to [cap_uperms_shift]+[cap_uperms_width]-1 of *rd* are set
 * equal to the **uperms** field of *cs1*.
 * The other bits of *rd* are set to zero.
 */
function clause execute (CGetPerm(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = EXTZ(getCapPerms(capVal));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the zero-extended **flags** field of
 * capability register *cs1*.
 */
function clause execute (CGetFlags(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = EXTZ(getCapFlags(capVal));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **otype** field of capability
 * register *cs1*.
 */
function clause execute (CGetType(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = if   hasReservedOType(capVal)
          then EXTS(capVal.otype)
          else EXTZ(capVal.otype);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **base** field of capability
 * register *cs1*.
 */
function clause execute (CGetBase(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = getCapBaseBits(capVal);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **offset** field of capability
 * register *cs1*.
 */
function clause execute (CGetOffset(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = getCapOffsetBits(capVal);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **high half** of capability
 * register *cs1*.
 *
 * The bits returned here are of the **in-memory** form of the capability, which
 * may differ from microarchitectural forms in use within implementations.
 * (Notably, in the sail implementation, see the distinction between [capToBits]
 * and [capToMemBits].)  That is, applying [CGetHigh] to a capability loaded
 * from address *m* will yield the same result as loading the high half of the
 * capability-sized granule at *m* (that is, bits above **XLEN** when a
 * capability is interpreted as a twice-**XLEN**-bit integer).
 */
function clause execute (CGetHigh(rd, cs1)) = {
  let capVal : Capability = C(cs1);
  X(rd) = capToMemBits(capVal)[sizeof(xlen) * 2 - 1 .. sizeof(xlen)];
  RETIRE_SUCCESS
}

union clause ast = CSetHigh : (regidx, regidx, regidx)
/*!
 * Capability register *cd* comes to hold the capability from *cs1* with its
 * high bits replaced with the value in the integer register *rs2*.  The tag
 * of *cd* is cleared.
 *
 * *rs2* holds the **in-memory** form of capability bits.  That is, this
 * instruction yields the same result as writing *cs1* out to memory,
 * overwriting the high word with *rs2*, and loading that capability-sized
 * granule into *cd*, although without the memory mutation side-effects.
 *
 */
function clause execute (CSetHigh(cd, cs1, rs2)) = {
  let capVal = C(cs1);
  let intVal = X(rs2);
  let capLow : xlenbits = capToMemBits(capVal)[sizeof(xlen) - 1 .. 0];
  let newCap : Capability = memBitsToCapability(false, intVal @ capLow);
  C(cd) = newCap;
  RETIRE_SUCCESS
}

/*
 * Note: We have to use [{xlen}][xlen] instead of [xlen] to avoid \lstinline{}
 * inside math mode.
 */
/*!
 * Integer register *rd* is set equal to the **length** field of capability
 * register *cs1*.
 *
 * ## Notes
 *
 * - Due to the compressed representation of capabilities, the actual length
 *   of capabilities can be $2^{[{xlen}][xlen]}$; [CGetLen] will return the
 *   maximum value of $2^{[{xlen}][xlen]}-1$ in this case.
 */
function clause execute (CGetLen(rd, cs1)) = {
  let capVal = C(cs1);
  let len = getCapLength(capVal);
  X(rd) = to_bits(sizeof(xlen), if len > cap_max_addr then cap_max_addr else len);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **top** field (i.e. one past the
 * last addressable byte) of capability register *cs1*.
 *
 * ## Notes
 *
 * - Due to the compressed representation of capabilities, the actual top
 *   of capabilities can be $2^{[{xlen}][xlen]}$; [CGetTop] will return the
 *   maximum value of $2^{[{xlen}][xlen]}-1$ in this case.
 */
function clause execute (CGetTop(rd, cs1)) = {
  let capVal = C(cs1);
  let top = getCapTop(capVal);
  X(rd) = to_bits(sizeof(xlen), if top > cap_max_addr then cap_max_addr else top);
  RETIRE_SUCCESS
}

/*!
 * The low bit of integer register *rd* is set to the **tag** field of *cs1*.
 * All other bits of *rd* are cleared.
 */
function clause execute (CGetTag(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = EXTZ(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

/*!
 * The low bit of integer register *rd* is set to 0 if *cs1* is unsealed
 * and to 1 otherwise.
 * All other bits of *rd* are cleared.
 */
function clause execute (CGetSealed(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = EXTZ(bool_to_bits(isCapSealed(capVal)));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **address** field of capability
 * register *cs1*.
 */
function clause execute (CGetAddr(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = capVal.address;
  RETIRE_SUCCESS
}

union clause ast = CSpecialRW : (regidx, screg, regidx)
/*!
 * Capability register *cd* is set equal to special capability register *scr*,
 * and *scr* is set equal to capability register *cs1* if *cs1* is not **C0**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *scr* does not exist.
 *   - *scr* is read-only and *cs1* is not **C0**.
 *   - *scr* is only accessible to a higher privilege mode.
 *   - *scr* requires **Permit_Access_System_Registers** and that is not
 *     granted by **PCC**.**perms**.
 *
 * ## Notes
 *
 * - Writing **NULL** to a special capability register cannot be done with **C0**
 *   as that only performs a read. An alternative implementation would allocate
 *   a separate two-operand CSpecialR instruction and interpret *cs1* being
 *   **C0** as a write of **NULL** if the need to use a temporary capability
 *   register proves to be overly problematic for software. For U-mode
 *   transitions to domains without **Permit_Access_System_Registers** only
 *   **DDC** should need clearing, which can be done with [CClear].
 */
function clause execute (CSpecialRW(cd, scr, cs1)) = {
  let (specialExists, ro, priv, needASR) : (bool, bool, Privilege, bool) = match unsigned(scr) {
    0  => (true, true,  User, false),
    1  => (true, false, User, false),
    4 if haveNExt() => (true, false, User, true),
    5 if haveNExt() => (true, false, User, true),
    6 if haveNExt() => (true, false, User, true),
    7 if haveNExt() => (true, false, User, true),
    12 if haveSupMode() => (true, false, Supervisor, true),
    13 if haveSupMode() => (true, false, Supervisor, true),
    14 if haveSupMode() => (true, false, Supervisor, true),
    15 if haveSupMode() => (true, false, Supervisor, true),
    28 => (true, false, Machine, true),
    29 => (true, false, Machine, true),
    30 => (true, false, Machine, true),
    31 => (true, false, Machine, true),
    _  => (false, true, Machine, true)
  };
  if (not(specialExists) |
      ro & cs1 != zeros() |
      (privLevel_to_bits(cur_privilege) <_u privLevel_to_bits(priv))) then {
    handle_illegal();
    RETIRE_FAIL
  } else if (needASR & not(pcc_access_system_regs())) then {
    handle_cheri_cap_exception(CapEx_AccessSystemRegsViolation, 0b1 @ scr);
    RETIRE_FAIL
  } else {
    let cs1_val = C(cs1);
    C(cd) = match unsigned(scr) {
      0  => {
        let (success, pcc) = setCapAddr(PCC, PC);
        assert (success, "PCC with offset PC should always be representable");
        pcc
      },
      1  => DDC,
      4  => UTCC,
      5  => UTDC,
      6  => UScratchC,
      7  => legalize_epcc(UEPCC),
      12 => STCC,
      13 => STDC,
      14 => SScratchC,
      15 => legalize_epcc(SEPCC),
      28 => MTCC,
      29 => MTDC,
      30 => MScratchC,
      31 => legalize_epcc(MEPCC),
      _  => {assert(false, "unreachable"); undefined}
    };
    if (cs1 != zeros()) then {
      match unsigned(scr) {
        1  => DDC = cs1_val,
        4  => UTCC = legalize_tcc(UTCC, cs1_val),
        5  => UTDC = cs1_val,
        6  => UScratchC = cs1_val,
        7  => UEPCC = cs1_val,
        12 => STCC = legalize_tcc(STCC, cs1_val),
        13 => STDC = cs1_val,
        14 => SScratchC = cs1_val,
        15 => SEPCC = cs1_val,
        28 => MTCC = legalize_tcc(MTCC, cs1_val),
        29 => MTDC = cs1_val,
        30 => MScratchC = cs1_val,
        31 => MEPCC = cs1_val,
        _  => assert(false, "unreachable")
      }
    };
    RETIRE_SUCCESS
  }
}

union clause ast = CAndPerm : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the **perms** field set to the bitwise and of its
 * previous value and bits 0 to [cap_hperms_width]-1 of integer register *rs2*
 * and the **uperms** field set to the bitwise and of its previous value and
 * bits [cap_uperms_shift] to [cap_uperms_shift]+[cap_uperms_width]-1 of *rs2*.
 * If *cs1* was sealed then *cd*.**tag** is cleared.
 */
function clause execute(CAndPerm(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let perms = getCapPerms(cs1_val);
  let mask = truncate(rs2_val, cap_perms_width);

  let inCap = clearTagIfSealed(cs1_val);
  let newCap = setCapPerms(inCap, (perms & mask));

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = CSetFlags : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the **flags** field set to bits 0 to [cap_flags_width]-1
 * of integer register *rs2*. If *cs1* was sealed then *cd*.**tag** is cleared.
 */
function clause execute(CSetFlags(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let newCap = setCapFlags(inCap, truncate(rs2_val, cap_flags_width));

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = CToPtr : (regidx, regidx, regidx)
/*!
 * If the **tag** field of capability register *cs1* is not set, integer
 * register *rd* is set to 0, otherwise integer register *rd* is set to
 * *cs1*.**address** $-$ *cs2*.**base**.
 *
 * ## Notes
 *
 * - *cs2* being sealed will not set *rd* to 0. This is for further study.
 */
function clause execute(CToPtr(rd, cs1, cs2)) = {
  let cs2_val = if unsigned(cs2) == 0 then DDC else C(cs2);
  let cs1_val = C(cs1);

  /* Note: returning zero for untagged values breaks magic constants such as SIG_IGN */
  X(rd) = if not(cs1_val.tag) then
            zeros()
          else
            cs1_val.address - getCapBaseBits(cs2_val);
  RETIRE_SUCCESS
}

union clause ast = CSub : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set equal to (*cs1*.**address** $-$
 * *cs2*.**address**) $\bmod~2^{[{xlen}][xlen]}$.
 */
function clause execute(CSub(rd, cs1, cs2)) = {
  let cs2_val = C(cs2);
  let cs1_val = C(cs1);

  X(rd) = cs1_val.address - cs2_val.address;
  RETIRE_SUCCESS
}

union clause ast = CIncOffset : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *rs2* decodes to.
 */
function clause execute (CIncOffset(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapOffset(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CIncOffsetImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *imm*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *imm* decodes to.
 */
function clause execute (CIncOffsetImmediate(cd, cs1, imm)) = {
  let cs1_val = C(cs1);
  let immBits : xlenbits = EXTS(imm);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapOffset(inCap, immBits);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CSetOffset : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**base** $+$ *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**base** $+$ *rs2* decodes to.
 */
function clause execute (CSetOffset(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = setCapOffset(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CSetAddr : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *rs2* decodes to.
 */
function clause execute (CSetAddr(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let (representable, newCap) = setCapAddr(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}


union clause ast = CSetBounds : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with integer register *rs2*. If the resulting capability cannot be
 * represented exactly the **base** will be rounded down and the **length**
 * will be rounded up by the smallest amount needed to form a representable
 * capability covering the requested bounds. The **tag** field of the result
 * is cleared if the bounds of the result exceed the bounds of *cs1*, or if
 * *cs1* was sealed.
 */
function clause execute (CSetBounds(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rs2_val);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(rs2_val));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newTop);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with *uimm*. If the resulting capability cannot be represented
 * exactly the **base** will be rounded down and the **length** will be rounded
 * up by the smallest amount needed to form a representable capability covering
 * the requested bounds. The **tag** field of the result is cleared if the
 * bounds of the result exceed the bounds of *cs1*, or if *cs1* was sealed.
 */
function clause execute (CSetBoundsImmediate(cd, cs1, uimm)) = {
  let cs1_val = C(cs1);

  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(uimm);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(uimm));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newTop);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsExact : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with integer register *rs2*. If the resulting capability cannot be
 * represented exactly, the **tag** field will be cleared (unlike
 * [CSetBounds]), the **base** will be rounded down and the **length** will be
 * rounded up by the smallest amount needed to form a representable capability
 * covering the requested bounds. The **tag** field of the result is cleared
 * if the bounds of the result exceed the bounds of *cs1*, or if *cs1* was
 * sealed.
 */
function clause execute (CSetBoundsExact(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rs2_val);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(rs2_val));

  let inCap = clearTagIfSealed(cs1_val);
  let (exact, newCap) = setCapBounds(inCap, newBase, newTop);

  C(cd) = clearTagIf(newCap, not(inBounds & exact));
  RETIRE_SUCCESS
}

union clause ast = CClearTag : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of *cs1*, with
 * the **tag** field cleared.
 */
function clause execute (CClearTag(cd, cs1)) = {
  let cs1_val = C(cs1);
  C(cd) = clearTag(cs1_val);
  RETIRE_SUCCESS
}

union clause ast = CMove : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of *cs1*.
 */
function clause execute (CMove(cd, cs1)) = {
  C(cd) = C(cs1);
  RETIRE_SUCCESS
}

union clause ast = CClear : (bits(2), bits(8))
/*!
 * Capability registers 8 $\times$ *q* $+$ *i* are each set to **NULL** if the
 * *i*th bit of *m* is set, with the exception that the 0th bit of *m* refers
 * to **DDC** when *q* is 0, rather than **C0**.
 *
 * ## Notes
 *
 * - This instruction is designed to accelerate the register clearing that is
 *   required for secure domain transitions. It is expected that it can be
 *   implemented efficiently in hardware using a single \`valid' bit per
 *   register that is cleared by this instruction and set on any subsequent
 *   write to the register.
 */
function clause execute (CClear(q, m)) = {
  let q_u = unsigned(q);
  foreach (i from 0 to 7)
    if m[i] == bitone then
      if q_u == 0 & i == 0 then
        DDC = null_cap
      else
        C(8 * q_u + i) = null_cap;
  RETIRE_SUCCESS
}

union clause ast = FPClear : (bits(2), bits(8))
/*!
 * Floating-point registers 8 $\times$ *q* $+$ *i* are each set to 0 if the
 * *i*th bit of *m* is set.
 *
 * ## Notes
 *
 * - This instruction is designed to accelerate the register clearing that is
 *   required for secure domain transitions. It is expected that it can be
 *   implemented efficiently in hardware using a single \`valid' bit per
 *   register that is cleared by this instruction and set on any subsequent
 *   write to the register.
 *
 * - The 0 value written is FLEN bits wide, the largest supported by the
 *   implementation, such that the in-memory representation of the register is
 *   0, rather than a NaN-boxed narrower value.
 */
function clause execute (FPClear(q, m)) = {
  if haveFExt() then {
    foreach (i from 0 to 7)
      if m[i] == bitone then
        F(8 * unsigned(q) + i) = zeros();
    RETIRE_SUCCESS
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = CFromPtr : (regidx, regidx, regidx)
/*!
 * If the value of integer register *rs2* is 0 then capability register *cd* is
 * set to **NULL**. Otherwise capability register *cd* is set to capability
 * register *cs1* with its **offset** replaced with *rs2*. If the resulting
 * capability cannot be represented exactly, or if *cs1* was sealed, then
 * *cd*.**tag** is cleared. The remaining capability fields are set to what the
 * in-memory representation of *cs1* with the address set to *cd*.**address**
 * decodes to.
 */
function clause execute (CFromPtr(cd, cs1, rs2)) = {
  let cs1_val = if unsigned(cs1) == 0 then DDC else C(cs1);
  let rs2_val = X(rs2);

  if rs2_val == zeros() then {
    C(cd) = null_cap;
    RETIRE_SUCCESS
  } else {
    let inCap = clearTagIfSealed(cs1_val);
    let (success, newCap) = setCapOffset(inCap, rs2_val);
    C(cd) = clearTagIf(newCap, not(success));
    RETIRE_SUCCESS
  }
}

union clause ast = CBuildCap : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **base**, **length**, **address**, **perms**, **uperms** and **flags**
 * replaced with the corresponding fields in capability register *cs2*. If
 * *cs2* is a sentry then *cd* is also sealed as a sentry. If the resulting
 * capability is not a subset of *cs1* in bounds or permissions, or is not a
 * legally derivable capability, or if *cs1* did not have its **tag** field
 * set, or if *cs1* was sealed, *cd* is replaced with *cs2* with its **tag**
 * field cleared.
 *
 * ## Notes
 *
 * - Implementations may instead choose to set *cd* to *cs2* with its **tag**
 *   set after performing all checks, but the specification derives the result
 *   from *cs1* in order to convey the provenance associated with this
 *   operation.
 */
function clause execute (CBuildCap(cd, cs1, cs2)) = {
  let cs1_val = if unsigned(cs1) == 0 then DDC else C(cs1);
  let cs2_val = C(cs2);

  let authorityCap = cs1_val;
  let requestedCap' = {C(cs2) with tag=true};
  let requestedSentry = signed(requestedCap'.otype) == otype_sentry;
  let requestedCap = if requestedSentry then requestedCap' else unsealCap(requestedCap');

  let (authorityBase, authorityTop) = getCapBounds(authorityCap);
  let (requestedBase, requestedTop) = getCapBounds(requestedCap);
  let authorityPerms = getCapPerms(authorityCap);
  let requestedPerms = getCapPerms(requestedCap);
  let requestedFlags = getCapFlags(requestedCap);

  let subset = (requestedBase >= authorityBase)
             & (requestedTop <= authorityTop)
             & (requestedBase <= requestedTop) /* check for length < 0 - possible because requested might be untagged */
             & ((requestedPerms & authorityPerms) == requestedPerms);

  let inCap = clearTagIfSealed(authorityCap);
  let (exact, cd1) = setCapBounds(inCap, to_bits(cap_addr_width, requestedBase), to_bits(cap_len_width, requestedTop));
  let (_, cd2) = setCapOffset(cd1, getCapOffsetBits(requestedCap)); /* Ignore representability check, since Fast Rep Check not relevant */
  let cd3 = setCapPerms(cd2, requestedPerms);
  let cd4 = setCapFlags(cd3, requestedFlags);
  let cd5 = if requestedSentry then sealCap(cd4, to_bits(cap_otype_width, otype_sentry)) else cd4;
  let derivable = cd5 == requestedCap; /* True iff requestedCap has bounds not exceeding address space and no reserved bits set, and authority was tagged and unsealed */
  assert(not(derivable) | exact, "CBuildCap: setCapBounds was not exact"); /* If requestedCap was a derivable encoding then setBounds should be exact */
  let cd6 = if subset & derivable then cd5 else clearTag(requestedCap);

  C(cd) = cd6;
  RETIRE_SUCCESS
}

union clause ast = CCopyType : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the **address** set to *cs2*.**otype** and the
 * **tag** field cleared if *cs2* has a reserved **otype** or if *cs1*
 * was sealed.
 *
 * ## Notes
 *
 * - Reserved otypes always result in untagged capabilities, as, at the
 *   moment, all reserved otypes are constructed using ambiently-available
 *   actions. [CCSeal] knows how to work with these.
 */
function clause execute (CCopyType(cd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);

  let reserved = hasReservedOType(cs2_val);
  let otype : xlenbits = if reserved then EXTS(cs2_val.otype)
                                     else EXTZ(cs2_val.otype);

  let inCap = clearTagIfSealed(cs1_val);
  let (representable, newCap) = setCapAddr(inCap, otype);

  C(cd) = clearTagIf(newCap, reserved | not(representable));
  RETIRE_SUCCESS
}

union clause ast = CRRL : (regidx, regidx)
/*!
 * Integer register *rd* is set to the smallest value greater or equal to *rs1*
 * that can be used as a length to set exact bounds on a capability that has a
 * suitably aligned base (as obtained with the help of [CRAM]).
 */
function clause execute(CRRL(rd, rs1)) = {
  let len = X(rs1);
  X(rd) = getRepresentableLength(len);
  RETIRE_SUCCESS
}

union clause ast = CRAM : (regidx, regidx)
/*!
 * Integer register *rd* is set to a mask that can be used to round addresses
 * down to to a value that is sufficiently aligned to set exact bounds for the
 * nearest representable length of *rs1* (as obtained by [CRRL]).
 */
function clause execute(CRAM(rd, rs1)) = {
  let len = X(rs1);
  X(rd) = getRepresentableAlignmentMask(len);
  RETIRE_SUCCESS
}

union clause ast = CTestSubset : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set to 1 if the **tag** fields of capability
 * registers *cs1* and *cs2* are the same and the bounds and permissions of
 * *cs2* are a subset of those of *cs1*.
 *
 * ## Notes
 *
 * - The operand order for this instruction is reversed compared with the
 *   normal RISC-V comparison instructions, but this may be changed in future.
 *
 * - The **otype** field is ignored for this instruction, but an alternative
 *   implementation might wish to consider capabilities with distinct
 *   **otype**s as unordered as is done for the **tag** field.
 */
function clause execute (CTestSubset(rd, cs1, cs2)) = {
  let cs1_val = if unsigned(cs1) == 0 then DDC else C(cs1);
  let cs2_val = C(cs2);

  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  let (cs1_base, cs1_top) = getCapBounds(cs1_val);
  let cs2_perms = getCapPerms(cs2_val);
  let cs1_perms = getCapPerms(cs1_val);

  let result = if cs1_val.tag != cs2_val.tag then
                 0b0
               else if cs2_base < cs1_base then
                 0b0
               else if cs2_top > cs1_top then
                 0b0
               else if (cs2_perms & cs1_perms) != cs2_perms then
                 0b0
               else
                 0b1;

  X(rd) = EXTZ(result);
  RETIRE_SUCCESS
}

union clause ast = CSEQX : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set to 1 if the **tag** fields and in-memory
 * representations of capability registers *cs1* and *cs2* are identical,
 * including any reserved encoding bits, otherwise it is set to 0.
 */
function clause execute (CSEQX(rd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  X(rd) = EXTZ(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

union clause ast = CSeal : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1*, and is
 * sealed with **otype** equal to the **address** field of capability register
 * *cs2*. If *cs2* is unable to authorize the sealing, or if *cs1* was already
 * sealed, then the **tag** field of *cd* is cleared.
 */
function clause execute (CSeal(cd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);

  let cs2_cursor = getCapCursor(cs2_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);

  let permitted = cs2_val.tag
                & not(isCapSealed(cs2_val))
                & cs2_val.permit_seal
                & (cs2_cursor >= cs2_base)
                & (cs2_cursor < cs2_top)
                & (cs2_cursor <= cap_max_otype);

  let inCap = clearTagIfSealed(cs1_val);
  let newCap = sealCap(inCap, to_bits(cap_otype_width, cs2_cursor));

  C(cd) = clearTagIf(newCap, not(permitted));
  RETIRE_SUCCESS
}

union clause ast = CCSeal : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1*, and is
 * conditionally sealed with **otype** equal to the **address** field of
 * capability register *cs2*. The conditions under which the input is passed
 * through unaltered are intended to permit a fast branchless rederivation
 * sequence with multiple sealing authorities with a single [CBuildCap] and a
 * set of [CCopyType] and [CCSeal] pairs when swapping capabilities in from
 * disk. Other than these conditions, if *cs2* is unable to authorize the
 * sealing, the **tag** field of *cd* is cleared.
 *
 * ## Notes
 *
 * - The intent is that this is used for rederiving swapped-out capabilities,
 *   so the expectation is that this whole sequence is guarded by a check on
 *   whether the **tag** field of the capability was valid.
 *
 * - If the input to be conditionally sealed is already sealed it is passed
 *   through before any futher checks are made. This allows multiple [CCSeal]s
 *   in a chain, any of which can be the one to seal the initial input. The
 *   intent is that all of these [CCSeal]s' authorities will have been produced
 *   by [CCopyType]s of the same input (i.e., they will all attempt to seal to
 *   the same type), but that's not, strictly, required. Sealed capabilities
 *   with a reserved **otype** are also constructed directly by [CBuildCap].
 *
 * - To avoid the need to branch on whether the original capability was sealed,
 *   attempts to seal with the reserved unsealed **otype** will leave the
 *   capability unmodified rather than trap.
 *
 * - To avoid the need to check which is the correct authority, any sealing
 *   request where the **address** of capability register *cs2* is out of
 *   bounds will leave the capability unmodified rather than trap, as will
 *   attempts to seal with an invalid capability since it may have become
 *   unrepresentable but be within its reinterpreted bounds.
 */
function clause execute (CCSeal(cd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);

  let cs2_cursor = getCapCursor(cs2_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  let passthrough = not(cs2_val.tag)
                  | isCapSealed(cs1_val)
                  | (cs2_cursor < cs2_base)
                  | (cs2_cursor >= cs2_top)
                  | (signed(cs2_val.address) == otype_unsealed);
  if passthrough then {
    C(cd) = cs1_val;
    RETIRE_SUCCESS
  } else {
    let permitted = not(isCapSealed(cs2_val))
                  & cs2_val.permit_seal
                  & (cs2_cursor <= cap_max_otype);
    let newCap = sealCap(cs1_val, to_bits(cap_otype_width, cs2_cursor));
    C(cd) = clearTagIf(newCap, not(permitted));
    RETIRE_SUCCESS
  }
}

union clause ast = CUnseal : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1* and is
 * unsealed, using capability register *cs2* as the authority for the unsealing
 * operation. If *cs2*.**perms** does not grant **Global** then *cd*.**perms**
 * is stripped of **Global**. If *cs2* is unable to authorize the unsealing,
 * the **tag** field of *cd* is cleared.
 */
function clause execute (CUnseal(cd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  let cs2_cursor = getCapCursor(cs2_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  let permitted = cs2_val.tag
                & isCapSealed(cs1_val)
                & not(isCapSealed(cs2_val))
                & not(hasReservedOType(cs1_val))
                & (cs2_cursor == unsigned(cs1_val.otype))
                & cs2_val.permit_unseal
                & (cs2_cursor >= cs2_base)
                & (cs2_cursor < cs2_top);
  let new_global = cs1_val.global & cs2_val.global;
  let newCap = {unsealCap(cs1_val) with global=new_global};
  C(cd) = clearTagIf(newCap, not(permitted));
  RETIRE_SUCCESS
}

union clause ast = CSealEntry : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1* and
 * sealed as a sentry.
 */
function clause execute (CSealEntry(cd, cs1)) = {
  let cs1_val = C(cs1);
  let inCap = clearTagIfSealed(cs1_val);
  C(cd) = sealCap(inCap, to_bits(cap_otype_width, otype_sentry));
  RETIRE_SUCCESS
}

union clause ast = CInvoke : (regidx, regidx)
/*!
 * **PCC** is set equal to capability register *cs1* and unsealed with the 0th
 * bit of its **address** set to 0, whilst **C31** is set equal to capability
 * register *cs2* and unsealed. This provides a constrained form of
 * non-monotonicity, allowing for fast jumps between protection domains, with
 * *cs1* providing the target domain's code and *cs2* providing the target
 * domain's data. The capabilities must have a matching **otype** to ensure the
 * right data is provided for the given jump target.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs2*.**tag** is not set.
 *   - *cs1*.**otype** is reserved.
 *   - *cs2*.**otype** is reserved.
 *   - *cs1*.**otype** $\ne$ *cs2*.**otype**.
 *   - *cs1*.**perms** does not grant **Permit_CInvoke**.
 *   - *cs2*.**perms** does not grant **Permit_CInvoke**.
 *   - *cs1*.**perms** does not grant **Permit_Execute**.
 *   - *cs2*.**perms** grants **Permit_Execute**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ min_instruction_bytes $\gt$ *cs1*.**top**.
 *   - *cs1*.**base** is unaligned.
 *   - *cs1*.**address** is unaligned, ignoring bit 0.
 *
 * ## Notes
 *
 * - From the point of view of security, this needs to be an atomic operation
 *   (i.e. the caller cannot decide to just do some of it, because partial
 *   execution could put the system into an insecure state). From a hardware
 *   perspective, more complex domain-transition implementations (e.g., to
 *   implement function-call semantics or message passing) may need to perform
 *   multiple memory reads and writes, which might take multiple cycles and
 *   complicate control logic.
 */
function clause execute (CInvoke(cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  let newPC = [cs1_val.address with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cs1_val);
  if not(cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if not(cs2_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs2);
    RETIRE_FAIL
  } else if hasReservedOType(cs1_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if hasReservedOType(cs2_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs2);
    RETIRE_FAIL
  } else if cs1_val.otype != cs2_val.otype then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs1);
    RETIRE_FAIL
  } else if not(cs1_val.permit_cinvoke) then {
    handle_cheri_reg_exception(CapEx_PermitCInvokeViolation, cs1);
    RETIRE_FAIL
  } else if not(cs2_val.permit_cinvoke) then {
    handle_cheri_reg_exception(CapEx_PermitCInvokeViolation, cs2);
    RETIRE_FAIL
  } else if not(cs1_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs1);
    RETIRE_FAIL
  } else if cs2_val.permit_execute then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs2);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newPC, min_instruction_bytes())) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if newPCCBase[0] == bitone | (newPCCBase[1] == bitone & ~(haveRVC())) then {
    handle_cheri_reg_exception(CapEx_UnalignedBase, cs1);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    C(31) = unsealCap(cs2_val);
    nextPC = newPC;
    nextPCC = unsealCap(cs1_val);
    RETIRE_SUCCESS
  }
}

union clause ast = JALR_CAP : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the next instruction's **PCC** and
 * sealed as a sentry. **PCC** is replaced with the value of capability
 * register *cs1* with the 0th bit of its **address** set to 0 and is unsealed
 * if it is a sentry.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed and is not a sentry.
 *   - *cs1*.**perms** does not grant **Permit_Execute**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ min_instruction_bytes $\gt$ *cs1*.**top**.
 *   - *cs1*.**base** is unaligned.
 *   - *cs1*.**address** is unaligned, ignoring bit 0.
 */
function clause execute(JALR_CAP(cd, cs1)) = {
  execute(CJALR(zeros(), cs1, cd))
}

union clause ast = JALR_PCC : (regidx, regidx)
/*!
 * Integer register *rd* is replaced with the next instruction's
 * **PCC**.**offset**. **PCC**.**offset** is replaced with the value of
 * register *rs1* with the 0th bit set to 0.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **PCC**.**address** $+$ *rs1* $\lt$ **PCC**.**base**.
 *   - **PCC**.**address** $+$ *rs1* $+$ min_instruction_bytes $\gt$ **PCC**.**top**.
 *   - **PCC**.**address** $+$ *rs1* is unaligned, ignoring bit 0.
 */
function clause execute(JALR_PCC(rd, rs1)) = {
  execute(RISCV_JALR(zeros(), rs1, rd))
}

val handle_load_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, bool, word_width) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_load_data_via_cap(rd, auth_idx, auth_val, vaddrBits, is_unsigned, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if check_misaligned(vaddrBits, width) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Data)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for data load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) =>
      match (width, sizeof(xlen)) {
        (BYTE, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 1, aq, aq & rl, false), is_unsigned),
        (HALF, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 2, aq, aq & rl, false), is_unsigned),
        (WORD, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 4, aq, aq & rl, false), is_unsigned),
        (DOUBLE, 64) => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 8, aq, aq & rl, false), is_unsigned)
      }
  }
}

union clause ast = LoadDataDDC : (regidx, regidx, bool, word_width)
/*!
 * Integer register *rd* is replaced with the signed or unsigned byte,
 * halfword, word or doubleword located in memory at **DDC**.**address** $+$
 * *rs1*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Load**.
 *   - **DDC**.**address** $+$ *rs1* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *size* $\gt$ **DDC**.**top**.
 */
function clause execute (LoadDataDDC(rd, rs1, is_unsigned, width)) = {
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_load_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, is_unsigned, width)
}

union clause ast = LoadDataCap : (regidx, regidx, bool, word_width)
/*!
 * Integer register *rd* is replaced with the signed or unsigned byte,
 * halfword, word or doubleword located in memory at *cs1*.**address**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Load**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *size* $\gt$ *cs1*.**top**.
 */
function clause execute (LoadDataCap(rd, cs1, is_unsigned, width)) = {
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_load_data_via_cap(rd, 0b0 @ cs1, cs1_val, vaddr, is_unsigned, width)
}

val handle_load_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_load_cap_via_cap(cd, auth_idx, auth_val, vaddrBits) = {
  let aq : bool = false;
  let rl : bool = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Cap)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for cap load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, ptw_info) => {
      let c = mem_read_cap(addr, aq, aq & rl, false);
      match c {
        MemValue(v) => {
          let cr = clearTagIf(v, ptw_info.ptw_lc == PTW_LC_CLEAR | not(auth_val.permit_load_cap));
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = LoadCapDDC : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the capability located in memory
 * at **DDC**.**address** $+$ *rs1*, and if **DDC**.**perms** does not grant
 * **Permit_Load_Capability** then *cd*.**tag** is cleared.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Load**.
 *   - **DDC**.**address** $+$ *rs1* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ **CLEN** $/$ 8 $\gt$ **DDC**.**top**.
 *   - **DDC**.**address** $+$ *rs1* is unaligned, regardless of whether the
 *     implementation supports unaligned data accesses.
 */
function clause execute (LoadCapDDC(cd, rs1)) = {
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_load_cap_via_cap(cd, DDC_IDX, ddc_val, vaddr)
}

union clause ast = LoadCapCap : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the capability located in memory
 * at *cs1*.**address**, and if *cs1*.**perms** does not grant
 * **Permit_Load_Capability** then *cd*.**tag** is cleared.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Load**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 *   - *cs1*.**address** is unaligned, regardless of whether the implementation
 *     supports unaligned data accesses.
 */
function clause execute (LoadCapCap(cd, cs1)) = {
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_load_cap_via_cap(cd, 0b0 @ cs1, cs1_val, vaddr)
}

union clause ast = CLoadTags : (regidx, regidx)
/*!
 * Integer register *rd* is replaced with the tags of the capabilities located
 * in memory at and above *cs1*.**address**. The 0th bit corresponds to the
 * first capability in memory. The result is coherent with other processors, as
 * if the corresponding data words had also been loaded. The number of tags
 * loaded is implementation-defined; typical implementations are expected to
 * return the tags held in an L1 cache line, and so we use the constant
 * [caps_per_cache_line]. The number of tags loaded must be a power of two, at
 * least 1, and no more than **XLEN**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant both **Permit_Load** and
 *     **Permit_Load_Capability**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ [caps_per_cache_line] $\times$ **CLEN** $/$ 8
 *     $\gt$ *cs1*.**top**.
 *   - *cs1*.**address** is unaligned.
 *   - The page table entry for *cs1*.**address** would cause the tag to be
 *     cleared.
 *
 * ## Notes
 *
 * - In order to reduce DRAM traffic, implementations may choose to load only
 *   the tags and not the corresponding data, and may wish to not evict other
 *   cache lines by treating it as a non-temporal/streaming load.
 *
 * - Software can easily discover the number of tags loaded by an
 *   implementation by storing a series of **XLEN** capabilities to an aligned
 *   array and performing a [CLoadTags] operation. This need only be done once.
 *
 * - For heterogeneous multi-core or multi-processor systems, all cores must
 *   return the same number of tags, which will often be based on the smallest
 *   cache line size in the system.
 *
 * - Unlike [CLC][LoadCapImm], this instruction traps if tags will always be
 *   unset due to lacking **Permit_Load_Capability** or page table entry
 *   permissions, since that is likely indicative of a software bug that could
 *   lead to temporal safety vulnerabilities if capabilities are erroneously
 *   missed.
 */
function clause execute (CLoadTags(rd, cs1)) = {
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  let aq : bool = false;
  let rl : bool = false;
  if not(cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(cs1_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not(cs1_val.permit_load) then {
    handle_cheri_reg_exception(CapEx_PermitLoadViolation, cs1);
    RETIRE_FAIL
  } else if not(cs1_val.permit_load_cap) then {
    handle_cheri_reg_exception(CapEx_PermitLoadCapViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, vaddr, caps_per_cache_line * cap_size)) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if not(unsigned(vaddr) % (caps_per_cache_line * cap_size) == 0) then {
    handle_mem_exception(vaddr, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddr, Read(Cap)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for tags load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
    TR_Address(addr, ptw_info) => {
      if ptw_info.ptw_lc != PTW_LC_OK then {
        handle_mem_exception(vaddr, E_Extension(EXC_LOAD_CAP_PAGE_FAULT));
        RETIRE_FAIL
      } else {
        mtags : MemoryOpResult(bits(caps_per_cache_line)) = MemValue(zeros());

        foreach (i from 0 to (caps_per_cache_line - 1)) {
          match mtags {
            MemException(_) => (),
            MemValue(tags) => {
              match mem_read_cap(addr + i * cap_size, aq, aq & rl, false) {
                MemException(e) => mtags = MemException(e),
                MemValue(v) =>
                  mtags = MemValue([tags with i = bool_to_bit(v.tag)])
              }
            }
          }
        };

        match mtags {
          MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
          MemValue(v) => { X(rd) = EXTZ(v); RETIRE_SUCCESS }
        }
      }
    }
  }
}

/* avoid platform checks for reservation address misalignment */
function check_res_misaligned(vaddr : xlenbits, width : word_width) -> bool =
  match width {
    BYTE   => false,
    HALF   => vaddr[0] == bitone,
    WORD   => vaddr[0] == bitone | vaddr[1] == bitone,
    DOUBLE => vaddr[0] == bitone | vaddr[1] == bitone | vaddr[2] == bitone
  }

val handle_loadres_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, word_width) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_loadres_data_via_cap(rd, auth_idx, auth_val, vaddrBits, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  let is_unsigned = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if check_res_misaligned(vaddrBits, width) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Data)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for data load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) =>
      match (width, sizeof(xlen)) {
        (BYTE, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 1, aq, aq & rl, false), is_unsigned),
        (HALF, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 2, aq, aq & rl, false), is_unsigned),
        (WORD, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 4, aq, aq & rl, false), is_unsigned),
        (DOUBLE, 64) => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 8, aq, aq & rl, false), is_unsigned)
      }
  }
}

val handle_loadres_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits, bool, bool) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_loadres_cap_via_cap(cd, auth_idx, auth_val, vaddrBits, aq, rl) = {
  let is_unsigned = false;
if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Cap)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for cap load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, ptw_info) => {
      let c = mem_read_cap(addr, aq, aq & rl, false);
      match c {
        MemValue(v) => {
          let cr = if ptw_info.ptw_lc == PTW_LC_CLEAR
                   then clearTag(v) /* strip the tag */
                   else {
                     /* the Sail model currently reserves virtual addresses */
                     load_reservation(addr);
                     clearTagIf(v, not(auth_val.permit_load_cap))
                   };
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = LoadResDataDDC : (regidx, regidx, word_width)
function clause execute (LoadResDataDDC(rd, rs1, width)) = {
  if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_loadres_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = LoadResCapDDC : (regidx, regidx)
function clause execute (LoadResCapDDC(cd, rs1)) = {
  if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_loadres_cap_via_cap(cd, DDC_IDX, ddc_val, vaddr, false, false)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = LoadResCap : (regidx, regidx, word_width)
function clause execute (LoadResCap(rd, cs1, width)) = {
  if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address;
    handle_loadres_data_via_cap(rd, 0b0 @ cs1, cs1_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = LoadResCapCap : (regidx, regidx)
function clause execute (LoadResCapCap(cd, cs1)) = {
  if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address + X(cs1);
    handle_loadres_cap_via_cap(cd, 0b0 @ cs1, cs1_val, vaddr, false, false)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}


union clause ast = LoadResCapMode : (regidx, regidx, bool, bool)
/*
 * Perform a load reserved of capability via either cs1 or DDC+rs1 depending
 * on cap mode.
 */
function clause execute (LoadResCapMode(cd, rs1_cs1, aq, rl)) = {
  if haveAtomics() then {
    let (auth_val, vaddr, auth_idx) = get_cheri_mode_cap_addr(rs1_cs1, zeros());
    handle_loadres_cap_via_cap(cd, auth_idx, auth_val, vaddr, aq, rl)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

val handle_store_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, word_width) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_store_data_via_cap(rs2, auth_idx, auth_val, vaddrBits, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if check_misaligned(vaddrBits, width) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Write(Data)) {
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for data store") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea(addr, size, aq & rl, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
        MemValue(_) => {
          let rs2_val = X(rs2);
          let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
            (BYTE, _)     => mem_write_value(addr, 1, rs2_val[7..0],  aq & rl, rl, false),
            (HALF, _)     => mem_write_value(addr, 2, rs2_val[15..0], aq & rl, rl, false),
            (WORD, _)     => mem_write_value(addr, 4, rs2_val[31..0], aq & rl, rl, false),
            (DOUBLE, 64) => mem_write_value(addr, 8, rs2_val,        aq & rl, rl, false)
          };
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error("store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

union clause ast = StoreDataDDC : (regidx, regidx, word_width)
/*!
 * The byte, halfword, word or doubleword located in memory at
 * **DDC**.**address** $+$ *rs1* is replaced with integer register *rs2*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Store**.
 *   - **DDC**.**address** $+$ *rs1* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *size* $\gt$ **DDC**.**top**.
 */
function clause execute (StoreDataDDC(rs2, rs1, width)) = {
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_store_data_via_cap(rs2, DDC_IDX, ddc_val, vaddr, width)
}

union clause ast = StoreDataCap : (regidx, regidx, word_width)
/*!
 * The byte, halfword, word or doubleword located in memory at
 * *cs1*.**address** is replaced with integer register *rs2*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Store**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *size* $\gt$ *cs1*.**top**.
 */
function clause execute (StoreDataCap(rs2, cs1, width)) = {
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_store_data_via_cap(rs2, 0b0 @ cs1, cs1_val, vaddr, width)
}

val handle_store_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wreg, wmvt}
function handle_store_cap_via_cap(cs2, auth_idx, auth_val, vaddrBits) = {
  let cs2_val = C(cs2);
  let aq : bool = false;
  let rl : bool = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store_cap) & cs2_val.tag then {
    handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store_local_cap) & cs2_val.tag & not(cs2_val.global) then {
    handle_cheri_cap_exception(CapEx_PermitStoreLocalCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Write(if cs2_val.tag then Cap else Data)) {
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
        MemValue(_) => {
          let res : MemoryOpResult(bool) = mem_write_cap(addr, cs2_val, aq & rl, rl, false);
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error("store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

union clause ast = StoreCapDDC : (regidx, regidx)
/*!
 * The capability located in memory at **DDC**.**address** $+$ *rs1* is
 * replaced with capability register *cs2*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Store**.
 *   - **DDC**.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - **DDC**.**perms** does not grant **Permit_Store_Local_Capability**,
 *     *cs2*.**tag** is set and *cs2*.**perms** does not grant **Global**.
 *   - **DDC**.**address** $+$ *rs1* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ **CLEN** $/$ 8 $\gt$ **DDC**.**top**.
 */
function clause execute (StoreCapDDC(cs2, rs1)) = {
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_store_cap_via_cap(cs2, DDC_IDX, ddc_val, vaddr)
}

union clause ast = StoreCapCap : (regidx, regidx)
/*!
 * The capability located in memory at *cs1*.**address** is replaced with
 * capability register *cs2*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Store**.
 *   - *cs1*.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - *cs1*.**perms** does not grant **Permit_Store_Local_Capability**,
 *     *cs2*.**tag** is set and *cs2*.**perms** does not grant **Global**.
 *   - *cs1*.**address** $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ **CLEN** $\gt$ *cs1*.**top**.
 */
function clause execute (StoreCapCap(cs2, cs1)) = {
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_store_cap_via_cap(cs2, 0b0 @ cs1, cs1_val, vaddr)
}

union clause ast = LoadCapImm : (regidx, regidx, bits(12))
/*!
 * In integer mode, capability register *cd* is replaced with the capability
 * located in memory at **DDC**.**address** $+$ *rs1* $+$ *imm*, and if
 * **DDC**.**perms** does not grant **Permit_Load_Capability** then
 * *cd*.**tag** is cleared. In capability mode, capability register *cd* is
 * replaced with the capability located in memory at *cs1*.**address** $+$
 * *imm*, and if *cs1*.**perms** does not grant **Permit_Load_Capability** then
 * *cd*.**tag** is cleared.
 *
 * ## Exceptions
 *
 * In integer mode, an exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Load**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *imm* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$
 *     **DDC**.**top**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *imm* is unaligned, regardless of
 *     whether the implementation supports unaligned data accesses.
 *
 * In capability mode, an exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Load**.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 *   - *cs1*.**address** $+$ *imm* is unaligned, regardless of whether the
 *     implementation supports unaligned data accesses.
 */
function clause execute LoadCapImm(cd, rs1_cs1, imm) = {
  let offset : xlenbits = EXTS(imm);
  let (auth_val, vaddr, auth_idx) = get_cheri_mode_cap_addr(rs1_cs1, offset);
  handle_load_cap_via_cap(cd, auth_idx, auth_val, vaddr)
}

union clause ast = StoreCapImm : (regidx, regidx, bits(12))
/*!
 * In integer mode, the capability located in memory at **DDC**.**address** $+$
 * *rs1* $+$ *imm* is replaced with capability register *cs2*. In capability
 * mode, the capability located in memory at *cs1*.**address** $+$ *imm* is
 * replaced with capability register *cs2*.
 *
 * ## Exceptions
 *
 * In integer mode, an exception is raised if:
 *   - **DDC**.**tag** is not set.
 *   - **DDC** is sealed.
 *   - **DDC**.**perms** does not grant **Permit_Store**.
 *   - **DDC**.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - **DDC**.**perms** does not grant **Permit_Store_Local_Capability**,
 *     *cs2*.**tag** is set and *cs2*.**perms** does not grant **Global**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *imm* $\lt$ **DDC**.**base**.
 *   - **DDC**.**address** $+$ *rs1* $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$
 *     **DDC**.**top**.
 *
 * In capability mode, an exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Store**.
 *   - *cs1*.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - *cs1*.**perms** does not grant **Permit_Store_Local_Capability**,
 *     *cs2*.**tag** is set and *cs2*.**perms** does not grant **Global**.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 */
function clause execute StoreCapImm(cs2, rs1_cs1, imm) = {
  let offset : xlenbits = EXTS(imm);
  let (auth_val, vaddr, auth_idx) = get_cheri_mode_cap_addr(rs1_cs1, offset);
  handle_store_cap_via_cap(cs2, auth_idx, auth_val, vaddr)
}

val handle_store_cond_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, word_width) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_store_cond_data_via_cap(rs2, auth_idx, auth_val, vaddrBits, width) = {
  let size = word_width_bytes(width);
  let aq : bool = true; /* cheri-specific aq/rl */
  let rl : bool = true;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if check_res_misaligned(vaddrBits, width) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else if match_reservation(vaddrBits) == false then {
    X(rs2) = EXTZ(0b1);
    cancel_reservation();
    RETIRE_SUCCESS
  } else {
    match translateAddr(vaddrBits, Write(Data)) {
      TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for data store") },
      TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
      TR_Address(addr, _) => {
        let eares : MemoryOpResult(unit) = mem_write_ea(addr, size, aq & rl, rl, false);
        match (eares) {
          MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
          MemValue(_) => {
            let rs2_val = X(rs2);
            let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
              (BYTE, _)     => mem_write_value(addr, 1, rs2_val[7..0],  aq & rl, rl, false),
              (HALF, _)     => mem_write_value(addr, 2, rs2_val[15..0], aq & rl, rl, false),
              (WORD, _)     => mem_write_value(addr, 4, rs2_val[31..0], aq & rl, rl, false),
              (DOUBLE, 64)  => mem_write_value(addr, 8, rs2_val,        aq & rl, rl, false)
            };
            match (res) {
              MemValue(true)  => { X(rs2) = EXTZ(0b0); cancel_reservation(); RETIRE_SUCCESS },
              MemValue(false) => { X(rs2) = EXTZ(0b1); cancel_reservation(); RETIRE_SUCCESS },
              MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
            }
          }
        }
      }
    }
  }
}

function write_sc_cap_result(rd : regidx, cap_dest : bool, result : bits(1)) -> unit = {
  /* Some SC instructions re-use the source register as the destination. To
    ensure this works correctly for split register file implementations we
    need to be careful about writing to the correct register file. This is only
    a concern for store conditional of capabilities where the source register
    is a capability register but the destination may be either a capability or
    an general purpose register depending on the instruction. */
  if cap_dest then {
    C(rd) = int_to_cap(EXTZ(result));
  } else {
    X(rd) = EXTZ(result);
  }
}

val handle_store_cond_cap_via_cap : (regidx, regidx, capreg_idx, Capability, xlenbits, bool, bool, bool) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wreg, wmvt}
function handle_store_cond_cap_via_cap(rd, cs2, auth_idx, auth_val, vaddrBits, aq, rl, cap_dest) = {
  let cs2_val = C(cs2);
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store_cap) & cs2_val.tag then {
    handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not(auth_val.permit_store_local_cap) & cs2_val.tag & not(cs2_val.global) then {
    handle_cheri_cap_exception(CapEx_PermitStoreLocalCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else if match_reservation(vaddrBits) == false then {
    /* cannot happen in rmem */
    write_sc_cap_result(rd, cap_dest, 0b1);
    cancel_reservation();
    RETIRE_SUCCESS
  } else {
    match translateAddr(vaddrBits, Write(if cs2_val.tag then Cap else Data)) {
      TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
      TR_Address(addr, _) => {
        let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
        match (eares) {
          MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
          MemValue(_) => {
            let res : MemoryOpResult(bool) = mem_write_cap(addr, cs2_val, aq & rl, rl, false);
            match (res) {
              MemValue(true)  => {
                write_sc_cap_result(rd, cap_dest, 0b0);
                cancel_reservation();
                RETIRE_SUCCESS
              },
              MemValue(false) => {
                write_sc_cap_result(rd, cap_dest, 0b1);
                cancel_reservation();
                RETIRE_SUCCESS
              },
              MemException(e) => {
                handle_mem_exception(vaddrBits, e);
                RETIRE_FAIL
              }
            }
          }
        }
      }
    }
  }
}

union clause ast = StoreCondDataDDC : (regidx, regidx, word_width)
function clause execute StoreCondDataDDC(rs2, rs1, width) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    X(rs2) = EXTZ(0b1);
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_store_cond_data_via_cap(rs2, DDC_IDX, ddc_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = StoreCondCapDDC : (regidx, regidx)
function clause execute StoreCondCapDDC(cs2, rs1) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    C(cs2) = int_to_cap(EXTZ(0b1));
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_store_cond_cap_via_cap(cs2, cs2, DDC_IDX, ddc_val, vaddr, false, false, true)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = StoreCondCap : (regidx, regidx, word_width)
function clause execute StoreCondCap(rs2, cs1, width) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    X(rs2) = EXTZ(0b1);
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address;
    handle_store_cond_data_via_cap(rs2, 0b0 @ cs1, cs1_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = StoreCondCapCap : (regidx, regidx)
function clause execute StoreCondCapCap(cs2, cs1) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    C(cs2) = int_to_cap(EXTZ(0b1));
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address;
    handle_store_cond_cap_via_cap(cs2, cs2, 0b0 @ cs1, cs1_val, vaddr, false, false, true)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = StoreCondCapMode : (regidx, regidx, regidx, bool, bool)
function clause execute StoreCondCapMode(rd, cs2, rs1_cs1, aq, rl) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    X(rd) = EXTZ(0b1);
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let (auth_val, vaddr, auth_idx) = get_cheri_mode_cap_addr(rs1_cs1, zeros());
    handle_store_cond_cap_via_cap(rd, cs2, auth_idx, auth_val, vaddr, aq, rl, false);
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = AMOSwapCap : (regidx, regidx, regidx, bool, bool)
function clause execute AMOSwapCap(cd, cs2, rs1_cs1, aq, rl) = {
  if haveAtomics() then {
    let (auth_val, vaddr, auth_idx) = get_cheri_mode_cap_addr(rs1_cs1, zeros());
    let cs2_val = C(cs2);
    if not(auth_val.tag) then {
      handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
      RETIRE_FAIL
    } else if isCapSealed(auth_val) then {
      handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
      RETIRE_FAIL
    } else if not(auth_val.permit_load) then {
      handle_cheri_cap_exception(CapEx_PermitLoadViolation, auth_idx);
      RETIRE_FAIL
    } else if not(auth_val.permit_store) then {
      handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
      RETIRE_FAIL
    } else if not(auth_val.permit_store_cap) & cs2_val.tag then {
      handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, auth_idx);
      RETIRE_FAIL
    } else if not(auth_val.permit_store_local_cap) & cs2_val.tag & not(cs2_val.global) then {
      handle_cheri_cap_exception(CapEx_PermitStoreLocalCapViolation, auth_idx);
      RETIRE_FAIL
    } else if not(inCapBounds(auth_val, vaddr, cap_size)) then {
      handle_cheri_cap_exception(CapEx_LengthViolation, auth_idx);
      RETIRE_FAIL
    } else if not(is_aligned_addr(vaddr, cap_size)) then {
      handle_mem_exception(vaddr, E_SAMO_Addr_Align());
      RETIRE_FAIL
    } else {
      match translateAddr(vaddr, ReadWrite(Cap, if cs2_val.tag then Cap else Data)) {
        TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, ptw_info) => {
          let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq & rl, rl, false);
          match (eares) {
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            MemValue(_) => {
              let c = mem_read_cap(addr, aq, aq & rl, false);
              match c {
                MemValue(v) => {
                  let wres : MemoryOpResult(bool) = mem_write_cap(addr, cs2_val, aq & rl, rl, false);
                  match wres {
                    MemValue(_) => {
                      let cr = clearTagIf(v, ptw_info.ptw_lc == PTW_LC_CLEAR | not(auth_val.permit_load_cap));
                      C(cd) = cr;
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
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

/*
NB: Must be careful about order of matching because unused register
fields are re-used as additional function codes: more specific matches
must come before more general ones. In our case that means two-arg
instructions (that have 0x7f in func7 field) must come before
three-arg ones.
*/

/* Two arg */

mapping clause encdec = CGetPerm(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetType(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetBase(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetLen(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b00011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetTag(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b00100 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetSealed(rd, cs1) if (haveXcheri()) <-> 0b1111111 @ 0b00101 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetOffset(rd, cs1) if (haveXcheri()) <-> 0b1111111 @ 0b00110 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetFlags(rd, cs1)  if (haveXcheri()) <-> 0b1111111 @ 0b00111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetAddr(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b01111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetHigh(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b10111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetTop(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b11000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CMove(cd, cs1)      if (haveXcheri()) <-> 0b1111111 @ 0b01010 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CClearTag(cd, cs1)  if (haveXcheri()) <-> 0b1111111 @ 0b01011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = JALR_CAP(cd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b01100 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSealEntry(cd, cs1) if (haveXcheri()) <-> 0b1111111 @ 0b10001 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = JALR_PCC(rd, rs1)   if (haveXcheri()) <-> 0b1111111 @ 0b10100 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CLoadTags(rd, cs1) if (haveXcheri()) <-> 0b1111111 @ 0b10010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CRRL(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CRAM(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CClear(q, m3 @ m5)  if (haveXcheri()) <-> 0b1111111 @ 0b01110 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri())
mapping clause encdec = FPClear(q, m3 @ m5) if (haveXcheri()) <-> 0b1111111 @ 0b10000 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri())

mapping clause assembly = CGetPerm(rd, cs1)   <-> "cgetperm"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetFlags(rd, cs1)  <-> "cgetflags"  ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetType(rd, cs1)   <-> "cgettype"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetBase(rd, cs1)   <-> "cgetbase"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetLen(rd, cs1)    <-> "cgetlen"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetTag(rd, cs1)    <-> "cgettag"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetSealed(rd, cs1) <-> "cgetsealed" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetOffset(rd, cs1) <-> "cgetoffset" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetAddr(rd, cs1)   <-> "cgetaddr"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetHigh(rd, cs1)   <-> "cgethigh"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetTop(rd, cs1)    <-> "cgettop"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CMove(cd, cs1)         <-> "cmove"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CClearTag(cd, cs1)     <-> "ccleartag"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = JALR_CAP(0b00000, cs1) <-> "jr.cap"     ^ spc() ^ cap_reg_name(cs1)
mapping clause assembly = JALR_CAP(cd, cs1)      <-> "jalr.cap"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CSealEntry(cd, cs1)    <-> "csealentry" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = JALR_PCC(0b00000, rs1) <-> "jr.pcc"     ^ spc() ^ reg_name(rs1)
mapping clause assembly = JALR_PCC(rd, rs1)      <-> "jalr.pcc"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = CLoadTags(rd, cs1) <-> "cloadtags" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ cap_reg_name(cs1) ^ ")"

mapping clause assembly = CRRL(rd, rs1) <-> "crrl" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = CRAM(rd, rs1) <-> "cram" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = CClear(q, m8)  <-> "cclear"  ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)
mapping clause assembly = FPClear(q, m8) <-> "fpclear" ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)

/* Three arg */

mapping clause encdec = CSeal(cd, cs1, cs2)       if (haveXcheri()) <-> 0b0001011 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CUnseal(cd, cs1, cs2)     if (haveXcheri()) <-> 0b0001100 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CAndPerm(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0001101 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetFlags(cd, cs1, rs2)   if (haveXcheri()) <-> 0b0001110 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetOffset(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0001111 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010000 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetHigh(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010110 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CIncOffset(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0010001 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBounds(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0001000 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsExact(cd, cs1, rs2) if (haveXcheri()) <-> 0b0001001 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CBuildCap(cd, cs1, cs2)   if (haveXcheri()) <-> 0b0011101 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCopyType(cd, cs1, cs2)   if (haveXcheri()) <-> 0b0011110 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCSeal(cd, cs1, cs2)      if (haveXcheri()) <-> 0b0011111 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CToPtr(rd, cs1, cs2)      if (haveXcheri()) <-> 0b0010010 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CFromPtr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010011 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSub(rd, cs1, cs2)        if (haveXcheri()) <-> 0b0010100 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CTestSubset(rd, cs1, cs2) if (haveXcheri()) <-> 0b0100000 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSpecialRW(cd, scr, cs1)  if (haveXcheri()) <-> 0b0000001 @ scr @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CIncOffsetImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b001 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b010 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CSEQX(rd, cs1, cs2) if (haveXcheri()) <-> 0b0100001 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause assembly = CSeal(cd, cs1, cs2)      <-> "cseal"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CUnseal(cd, cs1, cs2)    <-> "cunseal"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CAndPerm(cd, cs1, rs2)   <-> "candperm"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetFlags(cd, cs1, rs2)  <-> "csetflags"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetOffset(cd, cs1, rs2) <-> "csetoffset" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetAddr(cd, cs1, rs2)   <-> "csetaddr"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetHigh(cd, cs1, rs2)  <-> "csethigh"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CIncOffset(cd, cs1, rs2) <-> "cincoffset" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBounds(cd, cs1, rs2) <-> "csetbounds" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBoundsExact(cd, cs1, rs2) <-> "csetboundsexact" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CBuildCap(cd, cs1, cs2) <-> "cbuildcap"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CCopyType(cd, cs1, cs2) <-> "ccopytype"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CCSeal(cd, cs1, cs2)    <-> "ccseal"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CToPtr(rd, cs1, cs2)    <-> "ctoptr"      ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CFromPtr(cd, cs1, rs2)  <-> "cfromptr"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSub(rd, cs1, cs2)      <-> "csub"        ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CTestSubset(rd, cs1, cs2) <-> "ctestsubset" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CSpecialRW(cd, scr, cs1) <-> "cspecialrw"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ scr_name_map(scr) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CIncOffsetImmediate(cd, cs1, imm12) <-> "cincoffsetimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)
mapping clause assembly = CSetBoundsImmediate(cd, cs1, imm12) <-> "csetboundsimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = CSEQX(rd, cs1, cs2) <-> "cseqx" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

/* Two source */

mapping clause encdec = CInvoke(cs1, cs2)   if (haveXcheri()) <-> 0b1111110 @ cs2 @ cs1 @ 0b000 @ 0b00001 @ 0b1011011 if (haveXcheri())

mapping clause assembly = CInvoke(cs1, cs2) <-> "cinvoke" ^ spc() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

/* Loads and stores */

let haveRV128 = sizeof(xlen) >= 128
let haveRV64  = sizeof(xlen) >= 64

mapping clause encdec = LoadDataDDC(rd, rs1, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lb.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b00001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lh.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b00010 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lw.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b00011 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64) /* ld.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b00100 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbu.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b00101 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhu.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b00110 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwu.ddc */
mapping clause encdec = LoadDataDDC(rd, rs1, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b00111 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* ldu.ddc */
mapping clause encdec = LoadCapDDC(cd, rs1)                 if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b10111 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lc.ddc */
mapping clause encdec = LoadCapDDC(cd, rs1)                 if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b00011 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* lc.ddc */

mapping clause encdec = LoadDataCap(rd, cs1, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b01000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lb.cap */
mapping clause encdec = LoadDataCap(rd, cs1, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b01001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lh.cap */
mapping clause encdec = LoadDataCap(rd, cs1, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b01010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lw.cap */
mapping clause encdec = LoadDataCap(rd, cs1, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b01011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* ld.cap */
mapping clause encdec = LoadDataCap(rd, cs1, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b01100 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbu.cap */
mapping clause encdec = LoadDataCap(rd, cs1, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b01101 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhu.cap */
mapping clause encdec = LoadDataCap(rd, cs1, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b01110 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwu.cap */
mapping clause encdec = LoadDataCap(rd, cs1, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b01111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* ldu.cap */
mapping clause encdec = LoadCapCap(cd, cs1)                 if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b11111 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lc.cap */
mapping clause encdec = LoadCapCap(cd, cs1)                 if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b01011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* lc.cap */

mapping clause encdec = LoadResDataDDC(rd, rs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.b.ddc */
mapping clause encdec = LoadResDataDDC(rd, rs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.h.ddc */
mapping clause encdec = LoadResDataDDC(rd, rs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10010 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.w.ddc */
mapping clause encdec = LoadResDataDDC(rd, rs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111101 @ 0b10011 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64)  /* lr.d.ddc */
mapping clause encdec = LoadResCapDDC(cd, rs1)          if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b10011 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32)  /* lr.c.ddc */
mapping clause encdec = LoadResCapDDC(cd, rs1)          if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b10100 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64)  /* lr.c.ddc */

mapping clause encdec = LoadResCap(rd, cs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.b.cap */
mapping clause encdec = LoadResCap(rd, cs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.h.cap */
mapping clause encdec = LoadResCap(rd, cs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.w.cap */
mapping clause encdec = LoadResCap(rd, cs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111101 @ 0b11011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64)  /* lr.d.cap */
mapping clause encdec = LoadResCapCap(cd, cs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b11011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32)  /* lr.c.cap */
mapping clause encdec = LoadResCapCap(cd, cs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b11100 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64)  /* lr.c.cap */

mapping clause encdec = StoreDataDDC(rs2, rs1, BYTE)   if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00000 @ 0b1011011 if (haveXcheri()) /* sb.ddc */
mapping clause encdec = StoreDataDDC(rs2, rs1, HALF)   if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00001 @ 0b1011011 if (haveXcheri()) /* sh.ddc */
mapping clause encdec = StoreDataDDC(rs2, rs1, WORD)   if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00010 @ 0b1011011 if (haveXcheri()) /* sw.ddc */
mapping clause encdec = StoreDataDDC(rs2, rs1, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sd.ddc */
mapping clause encdec = StoreCapDDC(cs2, rs1)          if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b00100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sc.ddc */
mapping clause encdec = StoreCapDDC(cs2, rs1)          if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sc.ddc */

mapping clause encdec = StoreDataCap(rs2, cs1, BYTE)    if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01000 @ 0b1011011 if (haveXcheri()) /* sb.cap */
mapping clause encdec = StoreDataCap(rs2, cs1, HALF)    if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01001 @ 0b1011011 if (haveXcheri()) /* sh.cap */
mapping clause encdec = StoreDataCap(rs2, cs1, WORD)    if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01010 @ 0b1011011 if (haveXcheri()) /* sw.cap */
mapping clause encdec = StoreDataCap(rs2, cs1, DOUBLE)  if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sd.cap */
mapping clause encdec = StoreCapCap(cs2, cs1)           if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b01100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sc.cap */
mapping clause encdec = StoreCapCap(cs2, cs1)           if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sc.cap */

mapping clause encdec = StoreCondDataDDC(rs2, rs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10000 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.b.ddc */
mapping clause encdec = StoreCondDataDDC(rs2, rs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10001 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.h.ddc */
mapping clause encdec = StoreCondDataDDC(rs2, rs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10010 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.w.ddc */
mapping clause encdec = StoreCondDataDDC(rs2, rs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10011 @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64) /* sc.d.ddc */
mapping clause encdec = StoreCondCapDDC(cs2, rs1)          if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b10011 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) /* sc.c.ddc */
mapping clause encdec = StoreCondCapDDC(cs2, rs1)          if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b10100 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) /* sc.c.ddc */

mapping clause encdec = StoreCondCap(rs2, cs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11000 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.b.cap */
mapping clause encdec = StoreCondCap(rs2, cs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11001 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.h.cap */
mapping clause encdec = StoreCondCap(rs2, cs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11010 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.w.cap */
mapping clause encdec = StoreCondCap(rs2, cs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11011 @ 0b1011011 if (haveXcheri()  & haveAtomics()& haveRV64) /* sc.d.cap */
mapping clause encdec = StoreCondCapCap(cs2, cs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b11011 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) /* sc.c.cap */
mapping clause encdec = StoreCondCapCap(cs2, cs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b11100 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) /* sc.c.cap */

mapping clause assembly = LoadDataDDC(rd, rs1, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ ".ddc" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadDataCap(rd, cs1, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ ".cap" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadCapDDC(cd, rs1)        <-> "lc.ddc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadCapCap(cd, cs1)        <-> "lc.cap" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = LoadResDataDDC(rd, cs1, w) <-> "lr." ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadResCapDDC(cd, cs1)     <-> "lr.c.ddc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadResCap(rd, cs1, w)     <-> "lr." ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = LoadResCapCap(cd, cs1)     <-> "lr.c.cap" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = StoreDataDDC(rs2, rs1, w) <-> "s" ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreDataCap(rs2, cs1, w) <-> "s" ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapDDC(cs2, rs1)     <-> "sc.ddc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapCap(cs2, cs1)     <-> "sc.cap" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = StoreCondDataDDC(rs2, rs1, w) <-> "sc." ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCondCapDDC(cs2, rs1)     <-> "sc.c.ddc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCondCap(rs2, cs1, w)     <-> "sc." ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCondCapCap(cs2, cs1)     <-> "sc.c.cap" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause encdec = LoadCapImm(cd, rs1, offset) if sizeof(xlen) == 64 <-> offset @ rs1 @ 0b010 @ cd @ 0b0001111 if sizeof(xlen) == 64 /* lc */
mapping clause encdec = LoadCapImm(cd, rs1, offset) if sizeof(xlen) == 32 <-> offset @ rs1 @ 0b011 @ cd @ 0b0000011 if sizeof(xlen) == 32 /* lc */

mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 64 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b100 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 64 /* sc */
mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 32 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b011 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 32 /* sc */

mapping clause assembly = LoadCapImm(cd, rs1, offset)   <-> "lc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(cs2, rs1, offset) <-> "sc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

mapping clause encdec = LoadResCapMode(cd, rs1, aq, rl) if sizeof(xlen) == 32 <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b011 @ cd @ 0b0101111 if sizeof(xlen) == 32 /* lr.c (RV32) */
mapping clause encdec = LoadResCapMode(cd, rs1, aq, rl) if sizeof(xlen) == 64 <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b100 @ cd @ 0b0101111 if sizeof(xlen) == 64 /* lr.c (RV64) */

mapping clause encdec = StoreCondCapMode(rd, cs2, rs1, aq, rl) if sizeof(xlen) == 32 <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b011 @ rd @ 0b0101111 if sizeof(xlen) == 32 /* sc.c (RV32) */
mapping clause encdec = StoreCondCapMode(rd, cs2, rs1, aq, rl) if sizeof(xlen) == 64 <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b100 @ rd @ 0b0101111 if sizeof(xlen) == 64 /* sc.c (RV64) */

mapping clause encdec = AMOSwapCap(cd, cs2, rs1, aq, rl) if sizeof(xlen) == 32 <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b011 @ cd @ 0b0101111 if sizeof(xlen) == 32 /* sc.c (RV64) */
mapping clause encdec = AMOSwapCap(cd, cs2, rs1, aq, rl) if sizeof(xlen) == 64 <-> 0b00001 @ bool_bits(aq) @ bool_bits(rl) @ cs2 @ rs1 @ 0b100 @ cd @ 0b0101111 if sizeof(xlen) == 64 /* sc.c (RV64) */

mapping clause assembly = LoadResCapMode(cd, rs1, aq, rl) <-> "lr.c" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = StoreCondCapMode(rd, cs2, rs1, aq, rl) <-> "sc.c" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)
mapping clause assembly = AMOSwapCap(cd, cs2, rs1, aq, rl) <-> "amoswap.c" ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs2) ^ sep() ^ reg_name(rs1)

/*
  CHERI really needs sub word atomic operations because bounds checks mean you
  can't implement them in software with word sized operations. The RISC-V
  spec. does not define lr / sc for bytes or half words although the obvious
  encodings are vacant. Since the base Sail model actually implements the unused
  widths but refuses to decode them we can implement them for CHERI simply by
  adding the decodings here.
*/
mapping clause encdec = LOADRES(aq, rl, rs1, size, rd) if (size == BYTE) | (size == HALF)
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111 if (size == BYTE) | (size == HALF)
mapping clause encdec = STORECON(aq, rl, rs2, rs1, size, rd) if (size == BYTE) | (size == HALF)
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111 if (size == BYTE) | (size == HALF)

/*
 * Capability-mode specific encodings that overlap with baseline RISC-V
 * encodings. This does not include loads/stores since they are not decoded
 * differently, since the semantic differences are handled via hooks.
 */
val encdec_capmode : ast <-> bits(32) effect {rreg}
scattered mapping encdec_capmode

mapping clause encdec_capmode = AUIPCC(imm, cd) <-> imm @ cd @ 0b0010111
mapping clause assembly = AUIPCC(imm, cd)
  <-> "auipcc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_20(imm)
mapping clause encdec_capmode = CJALR(imm, cs1, cd) <-> imm @ cs1 @ 0b000 @ cd @ 0b1100111
mapping clause assembly = CJALR(imm, cs1, cd)
  <-> "cjalr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm)
/* See `mapping clause encdec = RISCV_JAL` for why we have to use this syntax */
mapping clause encdec_capmode = CJAL(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, cd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ cd @ 0b1101111
mapping clause assembly = CJAL(imm, cd)
  <-> "cjal" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_21(imm)


/* Wildcard match for non-capmode encodings. */
union clause ast = CAPMODE_ILLEGAL : word
function clause execute CAPMODE_ILLEGAL(s) = { internal_error("should be unreachable"); RETIRE_FAIL }
mapping clause encdec_capmode = CAPMODE_ILLEGAL(s) <-> s
end encdec_capmode
