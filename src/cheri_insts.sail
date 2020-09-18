/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2019 Robert M. Norton                              */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

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

function clause execute (CGetPerm(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = EXTZ(getCapPerms(capVal));
  RETIRE_SUCCESS
}

function clause execute (CGetFlags(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = EXTZ(getCapFlags(capVal));
  RETIRE_SUCCESS
}

function clause execute (CGetType(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = if   hasReservedOType(capVal)
          then EXTS(capVal.otype)
          else EXTZ(capVal.otype);
  RETIRE_SUCCESS
}

function clause execute (CGetBase(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = getCapBaseBits(capVal);
  RETIRE_SUCCESS
}

function clause execute (CGetOffset(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = getCapOffsetBits(capVal);
  RETIRE_SUCCESS
}

function clause execute (CGetLen(rd, cs1)) =
{
  let capVal = C(cs1);
  let len  = getCapLength(capVal);
  X(rd) = to_bits(sizeof(xlen), if len > MAX_ADDR then MAX_ADDR else len);
  RETIRE_SUCCESS
}

function clause execute (CGetTag(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = EXTZ(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

function clause execute (CGetSealed(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = EXTZ(bool_to_bits(capVal.sealed));
  RETIRE_SUCCESS
}

function clause execute (CGetAddr(rd, cs1)) =
{
  let capVal = C(cs1);
  X(rd) = capVal.address;
  RETIRE_SUCCESS
}

union clause ast = CSpecialRW : (regidx, screg, regidx)
function clause execute (CSpecialRW(cd, scr, cs1)) =
{
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
      ro & cs1 != 0b00000 |
      (privLevel_to_bits(cur_privilege) <_u privLevel_to_bits(priv))) then {
    handle_illegal();
    RETIRE_FAIL
  } else if (needASR & not(pcc_access_system_regs())) then {
    handle_cheri_cap_exception(CapEx_AccessSystemRegsViolation, 0b1 @ scr);
    RETIRE_FAIL
  } else {
    let cs1_val = C(cs1);
    if (cd != 0b00000) then {
      // read special cap
      let special_val : Capability = match unsigned(scr) {
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
      C(cd) = special_val;
    };
    if (cs1 != 0b00000) then {
      // write special cap
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
function clause execute(CAndPerm(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let perms   = getCapPerms(cs1_val);
    let newCap  = setCapPerms(cs1_val, (perms & rs2_val[30..0]));
    C(cd) = newCap;
    RETIRE_SUCCESS
  }
}

union clause ast = CSetFlags : (regidx, regidx, regidx)
function clause execute(CSetFlags(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let newCap  = setCapFlags(cs1_val, truncate(rs2_val, num_flags));
    C(cd) = newCap;
    RETIRE_SUCCESS
  }
}

union clause ast = CToPtr : (regidx, regidx, regidx)
function clause execute(CToPtr(rd, cs1, cs2)) =
{
  let cs2_val = if unsigned(cs2) == 0 then DDC else C(cs2);
  let cs1_val = C(cs1);
  if not (cs2_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs2);
    RETIRE_FAIL
  } else if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let ctBase = getCapBaseBits(cs2_val);
    /* Note: returning zero for untagged values breaks magic constants such as SIG_IGN */
    X(rd) = if not (cs1_val.tag) then
              zeros()
            else
              cs1_val.address - ctBase;
    RETIRE_SUCCESS
  }
}

union clause ast = CSub : (regidx, regidx, regidx)
function clause execute(CSub(rd, cs1, cs2)) =
{
  let cs2_val = C(cs2);
  let cs1_val = C(cs1);
  X(rd) = cs1_val.address - cs2_val.address;
  RETIRE_SUCCESS
}

union clause ast = CIncOffset : (regidx, regidx, regidx)
function clause execute (CIncOffset(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let (success, newCap) = incCapOffset(cs1_val, rs2_val);
    if success then
        C(cd) = newCap
    else
        C(cd) = invalidateCap(newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CIncOffsetImmediate : (regidx, regidx, bits(12))
function clause execute (CIncOffsetImmediate(cd, cs1, imm)) =
{
  let cs1_val = C(cs1);
  let immBits : xlenbits = EXTS(imm);
  if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let (success, newCap) = incCapOffset(cs1_val, immBits);
    if success then
        C(cd) = newCap
    else
        C(cd) = invalidateCap(newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CSetOffset : (regidx, regidx, regidx)
function clause execute (CSetOffset(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let (success, newCap) = setCapOffset(cs1_val, rs2_val);
    if success then
        C(cd) = newCap
    else
        C(cd) = invalidateCap(newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CSetAddr : (regidx, regidx, regidx)
function clause execute (CSetAddr(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  if cs1_val.tag & cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let (representable, newCap) = setCapAddr(cs1_val, rs2_val);
    if representable then
        C(cd) = newCap
    else
        C(cd) = invalidateCap(newCap);
    RETIRE_SUCCESS
  }
}


union clause ast = CSetBounds : (regidx, regidx, regidx)
function clause execute (CSetBounds(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rs2_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newBase, unsigned(rs2_val))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else {
    let (_, newCap) = setCapBounds(cs1_val, newBase, newTop);
    C(cd) = newCap; /* ignore exact */
    RETIRE_SUCCESS
  }
}

union clause ast = CSetBoundsImmediate : (regidx, regidx, bits(12))
function clause execute (CSetBoundsImmediate(cd, cs1, imm)) =
{
  let cs1_val = C(cs1);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(imm);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newBase, unsigned(imm))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else {
    let (_, newCap) = setCapBounds(cs1_val, newBase, newTop);
    C(cd) = newCap; /* ignore exact */
    RETIRE_SUCCESS
  }
}

union clause ast = CSetBoundsExact : (regidx, regidx, regidx)
function clause execute (CSetBoundsExact(cd, cs1, rs2)) =
{
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);
  let newBase = cs1_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rs2_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(cs1_val, newBase, unsigned(rs2_val))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else {
    let (exact, newCap) = setCapBounds(cs1_val, newBase, newTop);
    if not (exact) then {
      handle_cheri_reg_exception(CapEx_InexactBounds, cs1);
      RETIRE_FAIL
    } else {
      C(cd) = newCap;
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CClearTag : (regidx, regidx)
function clause execute (CClearTag(cd, cs1)) =
{
  let cs1_val = C(cs1);
  C(cd) = {cs1_val with tag=false};
  RETIRE_SUCCESS
}

union clause ast = CMove : (regidx, regidx)
function clause execute (CMove(cd, cs1)) =
{
  C(cd) = C(cs1);
  RETIRE_SUCCESS
}

union clause ast = Clear : (bits(2), bits(8))
function clause execute (Clear(q, m)) =
{
  let q_u = unsigned(q);
  foreach (i from 0 to 7)
    if m[i] == bitone then
      if q_u == 0 & i == 0 & not(haveSplitRegFile) then
        DDC = null_cap
      else
        X(8 * q_u + i) = zeros();
  RETIRE_SUCCESS
}

union clause ast = CClear : (bits(2), bits(8))
function clause execute (CClear(q, m)) =
{
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
function clause execute (FPClear(q, m)) =
{
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
function clause execute (CFromPtr(cd, cs1, rs2)) =
{
  let cs1_val = if unsigned(cs1) == 0 then DDC else C(cs1);
  let rs2_val = X(rs2);
  if rs2_val == zeros() then {
    C(cd) = null_cap;
    RETIRE_SUCCESS
  } else if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else {
    let (success, newCap) = setCapOffset(cs1_val, rs2_val);
    if success then
        C(cd) = newCap
    else
        C(cd) = invalidateCap(newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CBuildCap : (regidx, regidx, regidx)
function clause execute (CBuildCap(cd, cs1, cs2)) =
{
  let cs1_val = if unsigned(cs1) == 0 then DDC else C(cs1);
  let cs2_val = C(cs2);
  let (cs1_base, cs1_top) = getCapBounds(cs1_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  let cs1_perms = getCapPerms(cs1_val);
  let cs2_perms = getCapPerms(cs2_val);
  let cs2_flags = getCapFlags(cs2_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if cs2_base < cs1_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if cs2_top > cs1_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if cs2_base > cs2_top then { /* check for length < 0 - possible because cs2 might be untagged */
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else if (cs2_perms & cs1_perms) != cs2_perms then {
    handle_cheri_reg_exception(CapEx_UserDefViolation, cs1);
    RETIRE_FAIL
  } else {
    let (exact, cd1) = setCapBounds(cs1_val, to_bits(cap_addr_width, cs2_base), to_bits(cap_len_width, cs2_top));
    let (representable, cd2) = setCapOffset(cd1, getCapOffsetBits(cs2_val));
    let cd3 = setCapPerms(cd2, cs2_perms);
    let cd4 = setCapFlags(cd3, cs2_flags);
    let cd5 = if cs2_val.otype == to_bits(otype_width, otype_sentry) then sealCap(cd4, to_bits(otype_width, otype_sentry)) else cd4;
    {
      assert(exact, "CBuildCap: setCapBounds was not exact"); /* base and top came from cs2 originally so will be exact */
      C(cd) = cd5;
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CCopyType : (regidx, regidx, regidx)
function clause execute (CCopyType(cd, cs1, cs2)) =
{
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  let (cs1_base, cs1_top) = getCapBounds(cs1_val);
  let cs2_otype = unsigned(cs2_val.otype);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if hasReservedOType(cs2_val) then {
    /*
     * Reserved otypes always get turned into derived-from-NULL capabilities,
     * regardless of the authority given in cs1, as, at the moment, all reserved
     * otypes are constructed using ambiently-available actions.
     * CCSeal knows how to work with these.
     */
    C(cd) = int_to_cap(EXTS(cs2_val.otype));
    RETIRE_SUCCESS
  } else if cs2_otype < cs1_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else if cs2_otype >= cs1_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs1);
    RETIRE_FAIL
  } else {
    let (success, cap) = setCapOffset(cs1_val, to_bits(cap_addr_width, cs2_otype - cs1_base));
    assert(success, "CopyType: offset is in bounds so should be representable");
    C(cd) = cap;
    RETIRE_SUCCESS
  }
}


union clause ast = CRRL : (regidx, regidx)
function clause execute(CRRL(rd, rs1)) =
{
  let len = X(rs1);
  X(rd) = getRepresentableLength(len);
  RETIRE_SUCCESS
}

union clause ast = CRAM : (regidx, regidx)
function clause execute(CRAM(rd, rs1)) =
{
  let len = X(rs1);
  X(rd) = getRepresentableAlignmentMask(len);
  RETIRE_SUCCESS
}

union clause ast = CTestSubset : (regidx, regidx, regidx)
function clause execute (CTestSubset(rd, cs1, cs2)) =
{
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
function clause execute (CSEQX(rd, cs1, cs2)) =
{
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  X(rd) = EXTZ(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

  /*
   * Common suffix of CSeal and CCSeal
   */
val CSeal_core : (regidx, regidx, Capability, regidx, Capability) -> Retired effect { rreg, wreg, escape }
function CSeal_core (cd, cs1, cs1_val, cs2, cs2_val) =
{
  let cs2_cursor = getCapCursor(cs2_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);

  if cs2_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs2);
    RETIRE_FAIL
  } else if not (cs2_val.permit_seal) then {
    handle_cheri_reg_exception(CapEx_PermitSealViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor < cs2_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor >= cs2_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor > max_otype then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else {
    C(cd) = sealCap(cs1_val, to_bits(otype_width, cs2_cursor));
    RETIRE_SUCCESS
  }
}

union clause ast = CSeal : (regidx, regidx, regidx)
function clause execute (CSeal(cd, cs1, cs2)) =
{
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if not (cs2_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs2);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else CSeal_core (cd, cs1, cs1_val, cs2, cs2_val)
}

union clause ast = CCSeal : (regidx, regidx, regidx)
function clause execute (CCSeal(cd, cs1, cs2)) =
{
  let cs1_val = C(cs1); /* Tagged but unsealed cap */
  let cs2_val = C(cs2); /* Authority */
  let cs2_cursor = getCapCursor(cs2_val);

    /*
     * The "conditional" aspects of CCSeal mean that we do some tests on the
     * thing to be sealed before we actually check the authority.
     */
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if cs1_val.sealed then {
    /*
     * If the input to be conditionally sealed is already sealed, just pass it
     * through before any other checks are made.  This allows multiple CCSeal-s
     * in a chain, any of which can be the one to seal the initial input.  The
     * intent is that all of these CCSeal-s' authority caps will have been
     * produced by CCopyType of the same input (i.e., they will all attempt to
     * seal to the same type), but that's not, strictly, required.
     */
     C(cd) = cs1_val;
     RETIRE_SUCCESS

    /*
     * And now some special cases on the authority, before we get to checking
     * the conditions from CSeal
     */
  } else if cs2_val.address == to_bits(sizeof(xlen), otype_unsealed) then {
    /*
     * If the request is to seal to the unsealed type, just pass the result
     * through, without checking cs2_val's tag.  The authority is probably
     * the result of CCopyType from an unsealed capability and so cs1_val is
     * probably unsealed.
     */
    C(cd) = cs1_val;
    RETIRE_SUCCESS
  } else if not (cs2_val.tag) then {
    /*
     * An untagged authority can't seal anything, but likely represents an
     * authority taken so far out of bounds by CCopyType as to be
     * unrepresentable.  In that case, the caller may hold another authority
     * they wish to try, so just pass the result through.
     */
    C(cd) = cs1_val;
    RETIRE_SUCCESS
  } else CSeal_core (cd, cs1, cs1_val, cs2, cs2_val)
}

union clause ast = CUnseal : (regidx, regidx, regidx)
function clause execute (CUnseal(cd, cs1, cs2)) =
{
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  let cs2_cursor = getCapCursor(cs2_val);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if not (cs2_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs2);
    RETIRE_FAIL
  } else if not (cs1_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if cs2_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs2);
    RETIRE_FAIL
  } else if hasReservedOType(cs1_val) then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor != unsigned(cs1_val.otype) then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs2);
    RETIRE_FAIL
  } else if not (cs2_val.permit_unseal) then {
    handle_cheri_reg_exception(CapEx_PermitUnsealViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor < cs2_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else if cs2_cursor >= cs2_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs2);
    RETIRE_FAIL
  } else {
    let new_global = cs1_val.global & cs2_val.global;
    C(cd) = {unsealCap(cs1_val) with global=new_global};
    RETIRE_SUCCESS
  }
}

union clause ast = CSealEntry : (regidx, regidx)
function clause execute (CSealEntry(cd, cs1)) =
{
  let cs1_val = C(cs1);

  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if (cs1_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (cs1_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs1);
    RETIRE_FAIL
  } else {
    C(cd) = sealCap(cs1_val, to_bits(otype_width, otype_sentry));
    RETIRE_SUCCESS
  }
}

union clause ast = CInvoke : (regidx, regidx)
function clause execute (CInvoke(cs1, cs2)) =
{
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  let newPC = [cs1_val.address with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cs1_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if not (cs2_val.tag) then {
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
  } else if not (cs1_val.permit_cinvoke) then {
    handle_cheri_reg_exception(CapEx_PermitCInvokeViolation, cs1);
    RETIRE_FAIL
  } else if not (cs2_val.permit_cinvoke) then {
    handle_cheri_reg_exception(CapEx_PermitCInvokeViolation, cs2);
    RETIRE_FAIL
  } else if not (cs1_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs1);
    RETIRE_FAIL
  } else if cs2_val.permit_execute then {
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
    C(31) = unsealCap(cs1_val);
    nextPC = newPC;
    nextPCC = unsealCap(cs1_val);
    RETIRE_SUCCESS
  }
}

union clause ast = CJALR : (regidx, regidx)
function clause execute(CJALR(cd, cs1)) =
{
  let cs1_val = C(cs1);
  let newPC = [cs1_val.address with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cs1_val);
  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if (cs1_val.sealed & cs1_val.otype != to_bits(otype_width, otype_sentry)) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (cs1_val.permit_execute) then {
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
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instrucitons */
    assert(success, "Link cap should always be representable.");
    assert(not (linkCap.sealed), "Link cap should always be unsealed");
    C(cd) = sealCap(linkCap, to_bits(otype_width, otype_sentry));
    nextPC  = newPC;
    nextPCC = unsealCap(cs1_val);
    RETIRE_SUCCESS
  }
}

val handle_load_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, bool, word_width) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_load_data_via_cap(rd, auth_idx, auth_val, vaddrBits, is_unsigned, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
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
        (BYTE, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 1, aq, rl, false), is_unsigned),
        (HALF, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 2, aq, rl, false), is_unsigned),
        (WORD, _)    => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 4, aq, rl, false), is_unsigned),
        (DOUBLE, 64) => process_load(rd, vaddrBits, mem_read(Read(Data), addr, 8, aq, rl, false), is_unsigned)
      }
  }
}

union clause ast = CLoadDDC : (regidx, regidx, bool, word_width)
function clause execute (CLoadDDC(rd, rs1, is_unsigned, width)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_load_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, is_unsigned, width)
}

union clause ast = CLoadCap : (regidx, regidx, bool, word_width)
function clause execute (CLoadCap(rd, cs1, is_unsigned, width)) =
{
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
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
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
      let c = mem_read_cap(addr, aq, rl, false);
      match c {
        MemValue(v) => {
          let cr = if ptw_info == PTW_LOAD_CAP_ERR
                   then {v with tag = false} /* strip the tag */
                   else {v with tag = v.tag & auth_val.permit_load_cap};
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = CLoadCapDDC : (regidx, regidx)
function clause execute (CLoadCapDDC(cd, rs1)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_load_cap_via_cap(cd, DDC_IDX, ddc_val, vaddr)
}

union clause ast = CLoadCapCap : (regidx, regidx)
function clause execute (CLoadCapCap(cd, cs1)) =
{
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_load_cap_via_cap(cd, 0b0 @ cs1, cs1_val, vaddr)
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
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
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
        (BYTE, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 1, aq, rl, false), is_unsigned),
        (HALF, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 2, aq, rl, false), is_unsigned),
        (WORD, _)    => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 4, aq, rl, false), is_unsigned),
        (DOUBLE, 64) => process_loadres(rd, vaddrBits, mem_read(Read(Data), addr, 8, aq, rl, false), is_unsigned)
      }
  }
}

val handle_loadres_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_loadres_cap_via_cap(cd, auth_idx, auth_val, vaddrBits) = {
  let aq : bool = true;  /* cheri-specific aq/rl */
  let rl : bool = true;
  let is_unsigned = false;
if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
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
      let c = mem_read_cap(addr, aq, rl, false);
      match c {
        MemValue(v) => {
          let cr = if   ptw_info == PTW_LOAD_CAP_ERR
                   then {v with tag = false} /* strip the tag */
                   else {
                     /* the Sail model currently reserves virtual addresses */
                     load_reservation(addr);
                     {v with tag = v.tag & auth_val.permit_load_cap}
                   };
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = CLoadResDDC : (regidx, regidx, word_width)
function clause execute (CLoadResDDC(rd, rs1, width)) =
{
  if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_loadres_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = CLoadResCapDDC : (regidx, regidx)
function clause execute (CLoadResCapDDC(cd, rs1)) =
{
  if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_loadres_cap_via_cap(cd, DDC_IDX, ddc_val, vaddr)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = CLoadResCap : (regidx, regidx, word_width)
function clause execute (CLoadResCap(rd, cs1, width)) =
{
  if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address;
    handle_loadres_data_via_cap(rd, 0b0 @ cs1, cs1_val, vaddr, width)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = CLoadResCapCap : (regidx, regidx)
function clause execute (CLoadResCapCap(cd, cs1)) =
{
  if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address + X(cs1);
    handle_loadres_cap_via_cap(cd, 0b0 @ cs1, cs1_val, vaddr)
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
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
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
      let eares : MemoryOpResult(unit) = mem_write_ea(addr, size, aq, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
        MemValue(_) => {
          let rs2_val = X(rs2);
          let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
            (BYTE, _)     => mem_write_value(addr, 1, rs2_val[7..0],  aq, rl, false),
            (HALF, _)     => mem_write_value(addr, 2, rs2_val[15..0], aq, rl, false),
            (WORD, _)     => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, false),
            (DOUBLE, 64) => mem_write_value(addr, 8, rs2_val,        aq, rl, false)
          };
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error("store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

union clause ast = CStoreDDC : (regidx, regidx, word_width)
function clause execute (CStoreDDC(rs2, rs1, width)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_store_data_via_cap(rs2, DDC_IDX, ddc_val, vaddr, width)
}

union clause ast = CStoreCap : (regidx, regidx, word_width)
function clause execute (CStoreCap(rs2, cs1, width)) =
{
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
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store_cap) & cs2_val.tag then {
    handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store_local_cap) & cs2_val.tag & not(cs2_val.global) then {
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
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
        MemValue(_) => {
          let res : MemoryOpResult(bool) = mem_write_cap(addr, cs2_val, aq, rl, false);
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error("store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

union clause ast = CStoreCapDDC : (regidx, regidx)
function clause execute (CStoreCapDDC(cs2, rs1)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs1);
  handle_store_cap_via_cap(cs2, DDC_IDX, ddc_val, vaddr)
}

union clause ast = CStoreCapCap : (regidx, regidx)
function clause execute (CStoreCapCap(cs2, cs1)) =
{
  let cs1_val = C(cs1);
  let vaddr = cs1_val.address;
  handle_store_cap_via_cap(cs2, 0b0 @ cs1, cs1_val, vaddr)
}

union clause ast = CAP_AUIPC : (bits(20), regidx)
function clause execute CAP_AUIPC(imm, cd) = {
  let off : xlenbits = EXTS(imm @ 0x000);
  let ret = setCapAddrOrNull(PCC, PC + off);
  C(cd) = ret;
  RETIRE_SUCCESS
}

union clause ast = CLoadCapImm : (regidx, regidx, bits(12))
function clause execute CLoadCapImm(cd, rs1, off12) =
{
  let offset : xlenbits = EXTS(off12);
  let (auth_val, vaddr, cause_regno) = get_cheri_cap_addr(rs1, offset);
  handle_load_cap_via_cap(cd, cause_regno, auth_val, vaddr)
}

union clause ast = CStoreCapImm : (regidx, regidx, bits(12))
function clause execute CStoreCapImm(cs2, rs1, off12) =
{
  let offset : xlenbits = EXTS(off12);
  let (auth_val, vaddr, cause_regno) = get_cheri_cap_addr(rs1, offset);
  handle_store_cap_via_cap(cs2, cause_regno, auth_val, vaddr)
}

val handle_store_cond_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, word_width) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_store_cond_data_via_cap(rs2, auth_idx, auth_val, vaddrBits, width) = {
  let size = word_width_bytes(width);
  let aq : bool = true; /* cheri-specific aq/rl */
  let rl : bool = true;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
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
        let eares : MemoryOpResult(unit) = mem_write_ea(addr, size, aq, rl, false);
        match (eares) {
          MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
          MemValue(_) => {
            let rs2_val = X(rs2);
            let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
              (BYTE, _)     => mem_write_value(addr, 1, rs2_val[7..0],  aq, rl, false),
              (HALF, _)     => mem_write_value(addr, 2, rs2_val[15..0], aq, rl, false),
              (WORD, _)     => mem_write_value(addr, 4, rs2_val[31..0], aq, rl, false),
              (DOUBLE, 64)  => mem_write_value(addr, 8, rs2_val,        aq, rl, false)
            };
            match (res) {
              MemValue(true)  => { X(rs2) = EXTZ(0b0); cancel_reservation(); RETIRE_SUCCESS },
              MemValue(false) => { X(rs2) = EXTZ(0b1); cancel_reservation(); RETIRE_SUCCESS },
              MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL }
            }
          }
        }
      }
    }
  }
}

val handle_store_cond_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {eamem, escape, rmem, rmemt, rreg, wmv, wreg, wmvt}
function handle_store_cond_cap_via_cap(cs2, auth_idx, auth_val, vaddrBits) = {
  let cs2_val = C(cs2);
  let aq : bool = true; /* cheri-specific aq/rl */
  let rl : bool = true;
  if not(auth_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, auth_idx);
    RETIRE_FAIL
  } else if auth_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store_cap) & cs2_val.tag then {
    handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, auth_idx);
    RETIRE_FAIL
  } else if not (auth_val.permit_store_local_cap) & cs2_val.tag & not(cs2_val.global) then {
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
    C(cs2) = int_to_cap(EXTZ(0b1));
    cancel_reservation();
    RETIRE_SUCCESS
  } else {
    match translateAddr(vaddrBits, Write(if cs2_val.tag then Cap else Data)) {
      TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
      TR_Address(addr, _) => {
        let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq, rl, false);
        match (eares) {
          MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
          MemValue(_) => {
            let res : MemoryOpResult(bool) = mem_write_cap(addr, cs2_val, aq, rl, false);
            match (res) {
              MemValue(true)  => {
                 C(cs2) = int_to_cap(EXTZ(0b0));
                 cancel_reservation();
                 RETIRE_SUCCESS
              },
              MemValue(false) => {
                 C(cs2) = int_to_cap(EXTZ(0b1));
                 cancel_reservation();
                 RETIRE_SUCCESS
              },
              MemException(e) => {
                handle_mem_exception(addr, e);
                RETIRE_FAIL
              }
            }
          }
        }
      }
    }
  }
}

union clause ast = CStoreCondDDC : (regidx, regidx, word_width)
function clause execute CStoreCondDDC(rs2, rs1, width) =
{
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

union clause ast = CStoreCondCapDDC : (regidx, regidx)
function clause execute CStoreCondCapDDC(cs2, rs1) =
{
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    C(cs2) = int_to_cap(EXTZ(0b1));
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let ddc_val = DDC;
    let vaddr = ddc_val.address + X(rs1);
    handle_store_cond_cap_via_cap(cs2, DDC_IDX, ddc_val, vaddr)
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

union clause ast = CStoreCondCap : (regidx, regidx, word_width)
function clause execute CStoreCondCap(rs2, cs1, width) =
{
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

union clause ast = CStoreCondCapCap : (regidx, regidx)
function clause execute CStoreCondCapCap(cs2, cs1) =
{
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    C(cs2) = int_to_cap(EXTZ(0b1));
    RETIRE_SUCCESS
  } else if haveAtomics() then {
    let cs1_val = C(cs1);
    let vaddr = cs1_val.address;
    handle_store_cond_cap_via_cap(cs2, 0b0 @ cs1, cs1_val, vaddr)
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

mapping clause encdec = CMove(cd, cs1)      if (haveXcheri()) <-> 0b1111111 @ 0b01010 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CClearTag(cd, cs1)  if (haveXcheri()) <-> 0b1111111 @ 0b01011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CJALR(cd, cs1)      if (haveXcheri()) <-> 0b1111111 @ 0b01100 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSealEntry(cd, cs1) if (haveXcheri()) <-> 0b1111111 @ 0b10001 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CRRL(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CRAM(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = Clear(q, m3 @ m5)   if (haveXcheri()) <-> 0b1111111 @ 0b01101 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri())
mapping clause encdec = CClear(q, m3 @ m5)  if (haveXcheri() & haveSplitRegFile) <-> 0b1111111 @ 0b01110 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri() & haveSplitRegFile)
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

mapping clause assembly = CMove(cd, cs1)      <-> "cmove"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CClearTag(cd, cs1)  <-> "ccleartag"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CJALR(0b00000, cs1) <-> "cjr"        ^ spc() ^ cap_reg_name(cs1)
mapping clause assembly = CJALR(cd, cs1)      <-> "cjalr"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CSealEntry(cd, cs1) <-> "csealentry" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CRRL(rd, rs1) <-> "crrl" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = CRAM(rd, rs1) <-> "cram" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = Clear(q, m8)   <-> "clear"   ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)
mapping clause assembly = CClear(q, m8)  <-> "cclear"  ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)
mapping clause assembly = FPClear(q, m8) <-> "fpclear" ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)

/* Three arg */

mapping clause encdec = CSeal(cd, cs1, cs2)       if (haveXcheri()) <-> 0b0001011 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CUnseal(cd, cs1, cs2)     if (haveXcheri()) <-> 0b0001100 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CAndPerm(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0001101 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetFlags(cd, cs1, rs2)   if (haveXcheri()) <-> 0b0001110 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetOffset(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0001111 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010000 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
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

mapping clause encdec = CLoadDDC(rd, rs1, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lb.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b00001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lh.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b00010 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lw.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b00011 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64) /* ld.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b00100 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbu.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b00101 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhu.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b00110 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwu.ddc */
mapping clause encdec = CLoadDDC(rd, rs1, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b00111 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* ldu.ddc */
mapping clause encdec = CLoadCapDDC(cd, rs1)             if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b10111 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lc.ddc */
mapping clause encdec = CLoadCapDDC(cd, rs1)             if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b00011 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* lc.ddc */

mapping clause encdec = CLoadCap(rd, cs1, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b01000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lb.cap */
mapping clause encdec = CLoadCap(rd, cs1, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b01001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lh.cap */
mapping clause encdec = CLoadCap(rd, cs1, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b01010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lw.cap */
mapping clause encdec = CLoadCap(rd, cs1, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b01011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* ld.cap */
mapping clause encdec = CLoadCap(rd, cs1, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b01100 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbu.cap */
mapping clause encdec = CLoadCap(rd, cs1, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b01101 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhu.cap */
mapping clause encdec = CLoadCap(rd, cs1, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b01110 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwu.cap */
mapping clause encdec = CLoadCap(rd, cs1, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b01111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* ldu.cap */
mapping clause encdec = CLoadCapCap(cd, cs1)             if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b11111 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lc.cap */
mapping clause encdec = CLoadCapCap(cd, cs1)             if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b01011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* lc.cap */

mapping clause encdec = CLoadResDDC(rd, rs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.b.ddc */
mapping clause encdec = CLoadResDDC(rd, rs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.h.ddc */
mapping clause encdec = CLoadResDDC(rd, rs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b10010 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.w.ddc */
mapping clause encdec = CLoadResDDC(rd, rs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111101 @ 0b10011 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64)  /* lr.d.ddc */
mapping clause encdec = CLoadResCapDDC(cd, rs1) if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b10011 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32)  /* lr.c.ddc */
mapping clause encdec = CLoadResCapDDC(cd, rs1) if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b10100 @ rs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64)  /* lr.c.ddc */

mapping clause encdec = CLoadResCap(rd, cs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.b.cap */
mapping clause encdec = CLoadResCap(rd, cs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.h.cap */
mapping clause encdec = CLoadResCap(rd, cs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111101 @ 0b11010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics())  /* lr.w.cap */
mapping clause encdec = CLoadResCap(rd, cs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111101 @ 0b11011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64)  /* lr.d.cap */
mapping clause encdec = CLoadResCapCap(cd, cs1) if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b11011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32)  /* lr.c.cap */
mapping clause encdec = CLoadResCapCap(cd, cs1) if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b11100 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64)  /* lr.c.cap */

mapping clause encdec = CStoreDDC(rs2, rs1, BYTE)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00000 @ 0b1011011 if (haveXcheri()) /* sb.ddc */
mapping clause encdec = CStoreDDC(rs2, rs1, HALF)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00001 @ 0b1011011 if (haveXcheri()) /* sh.ddc */
mapping clause encdec = CStoreDDC(rs2, rs1, WORD)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00010 @ 0b1011011 if (haveXcheri()) /* sw.ddc */
mapping clause encdec = CStoreDDC(rs2, rs1, DOUBLE)     if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sd.ddc */
mapping clause encdec = CStoreCapDDC(cs2, rs1)          if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b00100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sc.ddc */
mapping clause encdec = CStoreCapDDC(cs2, rs1)          if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sc.ddc */

mapping clause encdec = CStoreCap(rs2, cs1, BYTE)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01000 @ 0b1011011 if (haveXcheri()) /* sb.cap */
mapping clause encdec = CStoreCap(rs2, cs1, HALF)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01001 @ 0b1011011 if (haveXcheri()) /* sh.cap */
mapping clause encdec = CStoreCap(rs2, cs1, WORD)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01010 @ 0b1011011 if (haveXcheri()) /* sw.cap */
mapping clause encdec = CStoreCap(rs2, cs1, DOUBLE)      if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sd.cap */
mapping clause encdec = CStoreCapCap(cs2, cs1)           if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b01100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sc.cap */
mapping clause encdec = CStoreCapCap(cs2, cs1)           if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sc.cap */

mapping clause encdec = CStoreCondDDC(rs2, rs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10000 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.b.ddc */
mapping clause encdec = CStoreCondDDC(rs2, rs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10001 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.h.ddc */
mapping clause encdec = CStoreCondDDC(rs2, rs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10010 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.w.ddc */
mapping clause encdec = CStoreCondDDC(rs2, rs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b10011 @ 0b1011011 if (haveXcheri() & haveAtomics() & haveRV64) /* sc.d.ddc */
mapping clause encdec = CStoreCondCapDDC(cs2, rs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b10011 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) /* sc.c.ddc */
mapping clause encdec = CStoreCondCapDDC(cs2, rs1)      if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ rs1 @ 0b000 @ 0b10100 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) /* sc.c.ddc */

mapping clause encdec = CStoreCondCap(rs2, cs1, BYTE)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11000 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.b.cap */
mapping clause encdec = CStoreCondCap(rs2, cs1, HALF)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11001 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.h.cap */
mapping clause encdec = CStoreCondCap(rs2, cs1, WORD)   if (haveXcheri() & haveAtomics()) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11010 @ 0b1011011 if (haveXcheri() & haveAtomics()) /* sc.w.cap */
mapping clause encdec = CStoreCondCap(rs2, cs1, DOUBLE) if (haveXcheri() & haveAtomics() & haveRV64) <-> 0b1111100 @ rs2 @ cs1 @ 0b000 @ 0b11011 @ 0b1011011 if (haveXcheri()  & haveAtomics()& haveRV64) /* sc.d.cap */
mapping clause encdec = CStoreCondCapCap(cs2, cs1)       if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b11011 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 32) /* sc.c.cap */
mapping clause encdec = CStoreCondCapCap(cs2, cs1)       if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) <-> 0b1111100 @ cs2 @ cs1 @ 0b000 @ 0b11100 @ 0b1011011 if (haveXcheri() & haveAtomics() & sizeof(xlen) == 64) /* sc.c.cap */

mapping clause assembly = CLoadDDC(rd, rs1, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ ".ddc" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadCap(rd, cs1, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ ".cap" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadCapDDC(cd, rs1)    <-> "lc.ddc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadCapCap(cd, cs1)    <-> "lc.cap" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = CLoadResDDC(rd, cs1, w) <-> "lr." ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadResCapDDC(cd, cs1) <-> "lr.c.ddc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadResCap(rd, cs1, w) <-> "lr." ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CLoadResCapCap(cd, cs1) <-> "lr.c.cap" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = CStoreDDC(rs2, rs1, w) <-> "s" ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCap(rs2, cs1, w) <-> "s" ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCapDDC(cs2, rs1) <-> "sc.ddc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCapCap(cs2, cs1) <-> "sc.cap" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause assembly = CStoreCondDDC(rs2, rs1, w) <-> "sc." ^ size_mnemonic(w) ^ ".ddc" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCondCapDDC(cs2, rs1) <-> "sc.c.ddc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCondCap(rs2, cs1, w) <-> "sc." ^ size_mnemonic(w) ^ ".cap" ^ spc() ^ reg_name(rs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCondCapCap(cs2, cs1) <-> "sc.c.cap" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ "(" ^ opt_spc() ^ cap_reg_name(cs1) ^ opt_spc() ^ ")"

mapping clause encdec = CLoadCapImm(cd, rs1, offset) if sizeof(xlen) == 64 <-> offset @ rs1 @ 0b010 @ cd @ 0b0001111 if sizeof(xlen) == 64 /* lc */
mapping clause encdec = CLoadCapImm(cd, rs1, offset) if sizeof(xlen) == 32 <-> offset @ rs1 @ 0b011 @ cd @ 0b0000011 if sizeof(xlen) == 32 /* lc */

mapping clause encdec = CStoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 64 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b100 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 64 /* sc */
mapping clause encdec = CStoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 32 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b011 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 32 /* sc */

mapping clause assembly = CLoadCapImm(cd, rs1, offset)   <-> "lc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCapImm(cs2, rs1, offset) <-> "sc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
