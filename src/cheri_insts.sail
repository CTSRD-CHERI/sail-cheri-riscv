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

function clause execute (CGetPerm(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = EXTZ(getCapPerms(capVal));
  RETIRE_SUCCESS
}

function clause execute (CGetFlags(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = EXTZ(getCapFlags(capVal));
  RETIRE_SUCCESS
}

function clause execute (CGetType(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = if   capVal.sealed
          then EXTZ(capVal.otype)
          else ones();
  RETIRE_SUCCESS
}

function clause execute (CGetBase(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = getCapBaseBits(capVal);
  RETIRE_SUCCESS
}

function clause execute (CGetOffset(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = getCapOffsetBits(capVal);
  RETIRE_SUCCESS
}

function clause execute (CGetLen(rd, cb)) =
{
  let capVal = readCapReg(cb);
  let len  = getCapLength(capVal);
  X(rd) = to_bits(sizeof(xlen), if len > MAX_ADDR then MAX_ADDR else len);
  RETIRE_SUCCESS
}

function clause execute (CGetTag(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = EXTZ(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

function clause execute (CGetSealed(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = EXTZ(bool_to_bits(capVal.sealed));
  RETIRE_SUCCESS
}

function clause execute (CGetAddr(rd, cb)) =
{
  let capVal = readCapReg(cb);
  X(rd) = capVal.address;
  RETIRE_SUCCESS
}
/*

union clause ast = CGetPCCSetOffset : (regidx, regidx)
function clause execute (CGetPCCSetOffset(cd, rs)) =
{
  checkCP2usable();
  let rs_val = rGPR(rs);
  let (success, newPCC) = setCapOffset(PCC, rs_val);
  if (success) then
    writeCapReg(cd, newPCC)
  else
    writeCapReg(cd, int_to_cap(rs_val));
  RETIRE_SUCCESS
}
/* Get and Set CP2 cause register */

union clause ast = CGetCause : regidx
function clause execute (CGetCause(rd)) =
{
  if not (pcc_access_system_regs ()) then {
    handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation);
    RETIRE_FAIL
  } else {
    X(rd) = EXTZ(CapCause.bits());
    RETIRE_SUCCESS
  }
}

union clause ast = CSetCause : regidx
function clause execute (CSetCause(rt)) =
{
  if not (pcc_access_system_regs ()) then {
    handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation);
    RETIRE_FAIL
  } else {
    let rt_val = X(rt);
    CapCause->ExcCode() = rt_val[15..8];
    CapCause->RegNum()  = rt_val[7..0];
    RETIRE_SUCCESS
  }
}

*/

union clause ast = CSpecialRW : (regidx, regidx, regidx)
function clause execute (CSpecialRW(cd, cs, idx)) =
{
  let (specialExists, ro, priv, needASR) : (bool, bool, Privilege, bool) = match unsigned(idx) {
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
  if (not(specialExists)) then {
    handle_illegal();
    RETIRE_FAIL
  } else if (ro & cs != 0b00000) |
     (privLevel_to_bits(cur_privilege) <_u privLevel_to_bits(priv)) |
     (needASR & not(pcc_access_system_regs())) then {
    handle_cheri_cap_exception(CapEx_AccessSystemRegsViolation, 0b1 @ idx);
    RETIRE_FAIL
  } else {
    let cs_val = readCapReg(cs);
    if (cd != 0b00000) then {
      // read special cap
      let special_val : Capability = match unsigned(idx) {
        0  => {
          let (success, pcc) = setCapAddr(PCC, PC);
          assert (success, "PCC with offset PC should always be representable");
          pcc
        },
        1  => DDC,
        4  => UTCC,
        5  => UTDC,
        6  => UScratchC,
        7  => UEPCC, /* XXX should mask offset as per uepc etc? */
        12 => STCC,
        13 => STDC,
        14 => SScratchC,
        15 => SEPCC,
        28 => MTCC,
        29 => MTDC,
        30 => MScratchC,
        31 => MEPCC,
        _  => {assert(false, "unreachable"); undefined}
      };
      writeCapReg(cd, special_val);
    };
    if (cs != 0b00000) then {
      // write special cap
      match unsigned(idx) {
        1  => DDC = cs_val,
        4  => UTCC = legalize_tcc(UTCC, cs_val),
        5  => UTDC = cs_val,
        6  => UScratchC = cs_val,
        7  => UEPCC = legalize_epcc(cs_val),
        12 => STCC = legalize_tcc(STCC, cs_val),
        13 => STDC = cs_val,
        14 => SScratchC = cs_val,
        15 => SEPCC = legalize_epcc(cs_val),
        28 => MTCC = legalize_tcc(MTCC, cs_val),
        29 => MTDC = cs_val,
        30 => MScratchC = cs_val,
        31 => MEPCC = legalize_epcc(cs_val),
        _  => assert(false, "unreachable")
      }
    };
    RETIRE_SUCCESS
  }
}

union clause ast = CAndPerm : (regidx, regidx, regidx)
function clause execute(CAndPerm(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let perms   = getCapPerms(cb_val);
    let newCap  = setCapPerms(cb_val, (perms & rt_val[30..0]));
    writeCapReg(cd, newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CSetFlags : (regidx, regidx, regidx)
function clause execute(CSetFlags(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let newCap  = setCapFlags(cb_val, truncate(rt_val, num_flags));
    writeCapReg(cd, newCap);
    RETIRE_SUCCESS
  }
}

union clause ast = CToPtr : (regidx, regidx, regidx)
function clause execute(CToPtr(rd, cb, ct)) =
{
  let ct_val = readCapRegDDC(ct);
  let cb_val = readCapReg(cb);
  if not (ct_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, ct);
    RETIRE_FAIL
  } else if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let ctBase = getCapBaseBits(ct_val);
    /* Note: returning zero for untagged values breaks magic constants such as SIG_IGN */
    X(rd) = if not (cb_val.tag) then
              zeros()
            else
              cb_val.address - ctBase;
    RETIRE_SUCCESS
  }
}

union clause ast = CSub : (regidx, regidx, regidx)
function clause execute(CSub(rd, cb, ct)) =
{
  let ct_val = readCapReg(ct);
  let cb_val = readCapReg(cb);
  X(rd) = cb_val.address - ct_val.address;
  RETIRE_SUCCESS
}

union clause ast = CIncOffset : (regidx, regidx, regidx)
function clause execute (CIncOffset(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let (success, newCap) = incCapOffset(cb_val, rt_val);
    if success then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(cb_val.address + rt_val));
    RETIRE_SUCCESS
  }
}

union clause ast = CIncOffsetImmediate : (regidx, regidx, bits(12))
function clause execute (CIncOffsetImmediate(cd, cb, imm)) =
{
  let cb_val = readCapReg(cb);
  let immBits : xlenbits = EXTS(imm);
  if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let (success, newCap) = incCapOffset(cb_val, immBits);
    if success then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(cb_val.address + immBits));
    RETIRE_SUCCESS
  }
}

union clause ast = CSetOffset : (regidx, regidx, regidx)
function clause execute (CSetOffset(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let (success, newCap) = setCapOffset(cb_val, rt_val);
    if success then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(getCapBaseBits(cb_val) + rt_val));
    RETIRE_SUCCESS
  }
}

union clause ast = CSetAddr : (regidx, regidx, regidx)
function clause execute (CSetAddr(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  if cb_val.tag & cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let (representable, newCap) = setCapAddr(cb_val, rt_val);
    if representable then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(rt_val));
    RETIRE_SUCCESS
  }
}


union clause ast = CSetBounds : (regidx, regidx, regidx)
function clause execute (CSetBounds(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  let newBase = cb_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rt_val);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if not(inCapBounds(cb_val, newBase, unsigned(rt_val))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else {
    let (_, newCap) = setCapBounds(cb_val, newBase, newTop);
    writeCapReg(cd, newCap); /* ignore exact */
    RETIRE_SUCCESS
  }
}

union clause ast = CSetBoundsImmediate : (regidx, regidx, bits(12))
function clause execute (CSetBoundsImmediate(cd, cb, imm)) =
{
  let cb_val = readCapReg(cb);
  let newBase= cb_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(imm);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if not(inCapBounds(cb_val, newBase, unsigned(imm))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else {
    let (_, newCap) = setCapBounds(cb_val, newBase, newTop);
    writeCapReg(cd, newCap); /* ignore exact */
    RETIRE_SUCCESS
  }
}

union clause ast = CSetBoundsExact : (regidx, regidx, regidx)
function clause execute (CSetBoundsExact(cd, cb, rt)) =
{
  let cb_val = readCapReg(cb);
  let rt_val = X(rt);
  let newBase = cb_val.address;
  let newTop : CapLenBits = EXTZ(newBase) + EXTZ(rt_val);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if not(inCapBounds(cb_val, newBase, unsigned(rt_val))) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else {
    let (exact, newCap) = setCapBounds(cb_val, newBase, newTop);
    if not (exact) then {
      handle_cheri_reg_exception(CapEx_InexactBounds, cb);
      RETIRE_FAIL
    } else {
      writeCapReg(cd, newCap);
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CClearTag : (regidx, regidx)
function clause execute (CClearTag(cd, cb)) =
{
  let cb_val = readCapReg(cb);
  writeCapReg(cd, {cb_val with tag=false});
  RETIRE_SUCCESS
}

union clause ast = CMove : (regidx, regidx)
function clause execute (CMove(cd, cb)) =
{
  writeCapReg(cd) = readCapReg(cb);
  RETIRE_SUCCESS
}

union clause ast = ClearRegs : (ClearRegSet, bits(2), bits(8))
function clause execute (ClearRegs(regset, q, m)) =
{
  /*
  if ((regset == CLo) | (regset == CHi)) then
    checkCP2usable();
  */
  foreach (i from 0 to 7)
    if m[i] == bitone then
      match regset {
        GPRegs => X(8 * unsigned(q) + i) = zeros(),
        FPRegs => () /* XXX no F regs yet */
      };
  RETIRE_SUCCESS
}

union clause ast = CFromPtr : (regidx, regidx, regidx)
function clause execute (CFromPtr(cd, cb, rt)) =
{
  let cb_val = readCapRegDDC(cb);
  let rt_val = X(rt);
  if rt_val == zeros() then {
    writeCapReg(cd, null_cap);
    RETIRE_SUCCESS
  } else if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else {
    let (success, newCap) = setCapOffset(cb_val, rt_val);
    if success then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(getCapBaseBits(cb_val) + rt_val));
    RETIRE_SUCCESS
  }
}

union clause ast = CBuildCap : (regidx, regidx, regidx)
function clause execute (CBuildCap(cd, cb, ct)) =
{
  let cb_val = readCapRegDDC(cb);
  let ct_val = readCapReg(ct);
  let (cb_base, cb_top) = getCapBounds(cb_val);
  let (ct_base, ct_top) = getCapBounds(ct_val);
  let cb_perms = getCapPerms(cb_val);
  let ct_perms = getCapPerms(ct_val);
  let ct_flags = getCapFlags(ct_val);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if ct_base < cb_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else if ct_top > cb_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else if ct_base > ct_top then { /* check for length < 0 - possible because ct might be untagged */
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if (ct_perms & cb_perms) != ct_perms then {
    handle_cheri_reg_exception(CapEx_UserDefViolation, cb);
    RETIRE_FAIL
  } else {
    let (exact, cd1) = setCapBounds(cb_val, to_bits(cap_addr_width, ct_base), to_bits(cap_len_width, ct_top));
    let (representable, cd2) = setCapOffset(cd1, getCapOffsetBits(ct_val));
    let cd3 = setCapPerms(cd2, ct_perms);
    let cd4 = setCapFlags(cd3, ct_flags);
    {
      assert(exact, "CBuildCap: setCapBounds was not exact"); /* base and top came from ct originally so will be exact */
      assert(representable, "CBuildCap: offset was not representable"); /* similarly offset should be representable XXX except for fastRepCheck */
      writeCapReg(cd, cd4);
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CCopyType : (regidx, regidx, regidx)
function clause execute (CCopyType(cd, cb, ct)) =
{
  let cb_val = readCapReg(cb);
  let ct_val = readCapReg(ct);
  let (cb_base, cb_top) = getCapBounds(cb_val);
  let ct_otype = unsigned(ct_val.otype);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if cb_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if ct_val.sealed then {
    if ct_otype < cb_base then {
      handle_cheri_reg_exception(CapEx_LengthViolation, cb);
      RETIRE_FAIL
    } else if ct_otype >= cb_top then {
      handle_cheri_reg_exception(CapEx_LengthViolation, cb);
      RETIRE_FAIL
    } else {
      let (success, cap) = setCapOffset(cb_val, to_bits(cap_addr_width, ct_otype - cb_base));
      assert(success, "CopyType: offset is in bounds so should be representable");
      writeCapReg(cd, cap);
      RETIRE_SUCCESS
    }
  } else {
    writeCapReg(cd, int_to_cap(ones()));
    RETIRE_SUCCESS
  }
}

union clause ast = CCheckPerm : (regidx, regidx)
function clause execute (CCheckPerm(cs, rt)) =
{
  let cs_val = readCapReg(cs);
  let cs_perms : xlenbits = EXTZ(getCapPerms(cs_val));
  let rt_perms = X(rt);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if (cs_perms & rt_perms) != rt_perms then {
    handle_cheri_reg_exception(CapEx_UserDefViolation, cs);
    RETIRE_FAIL
  } else
    RETIRE_SUCCESS
}

union clause ast = CCheckType : (regidx, regidx)
function clause execute (CCheckType(cs, cb)) =
{
  let cs_val = readCapReg(cs);
  let cb_val = readCapReg(cb);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if not (cs_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if cs_val.otype != cb_val.otype then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs);
    RETIRE_FAIL
  } else
    RETIRE_SUCCESS
}

union clause ast = CCheckTag : (regidx)
function clause execute (CCheckTag (cs)) =
{
  let cs_val = readCapReg(cs);
  if not(cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else
    RETIRE_SUCCESS
}

union clause ast = CTestSubset : (regidx, regidx, regidx)
function clause execute (CTestSubset(rd, cb, ct)) =
{
  let cb_val = readCapRegDDC(cb);
  let ct_val = readCapReg(ct);
  let (ct_base, ct_top) = getCapBounds(ct_val);
  let (cb_base, cb_top) = getCapBounds(cb_val);
  let ct_perms = getCapPerms(ct_val);
  let cb_perms = getCapPerms(cb_val);
  let result = if cb_val.tag != ct_val.tag then
                  0b0
               else if ct_base < cb_base then
                  0b0
               else if ct_top > cb_top then
                  0b0
               else if (ct_perms & cb_perms) != ct_perms then
                  0b0
               else
                  0b1;
  X(rd) = EXTZ(result);
  RETIRE_SUCCESS
}

union clause ast = CSeal : (regidx, regidx, regidx)
function clause execute (CSeal(cd, cs, ct)) =
{
  let cs_val = readCapReg(cs);
  let ct_val = readCapReg(ct);
  let ct_cursor = getCapCursor(ct_val);
  let (ct_base, ct_top) = getCapBounds(ct_val);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (ct_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, ct);
    RETIRE_FAIL
  } else if cs_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if ct_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, ct);
    RETIRE_FAIL
  } else if not (ct_val.permit_seal) then {
    handle_cheri_reg_exception(CapEx_PermitSealViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor < ct_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor >= ct_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor > max_otype then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else {
    let (success, newCap) = sealCap(cs_val, to_bits(24, ct_cursor));
    if not (success) then {
      handle_cheri_reg_exception(CapEx_InexactBounds, cs);
      RETIRE_FAIL
    } else {
      writeCapReg(cd, newCap);
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CCSeal : (regidx, regidx, regidx)
function clause execute (CCSeal(cd, cs, ct)) =
{
  let cs_val = readCapReg(cs);
  let ct_val = readCapReg(ct);
  let ct_cursor = getCapCursor(ct_val);
  let (ct_base, ct_top) = getCapBounds(ct_val);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (ct_val.tag) | (getCapCursor(ct_val) == MAX_ADDR) then {
    writeCapReg(cd, cs_val);
    RETIRE_SUCCESS
  } else if cs_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if ct_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, ct);
    RETIRE_FAIL
  } else if not (ct_val.permit_seal) then {
    handle_cheri_reg_exception(CapEx_PermitSealViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor < ct_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor >= ct_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor > max_otype then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else {
    let (success, newCap) = sealCap(cs_val, to_bits(24, ct_cursor));
    if not (success) then {
      handle_cheri_reg_exception(CapEx_InexactBounds, cs);
      RETIRE_FAIL
    } else {
      writeCapReg(cd, newCap);
      RETIRE_SUCCESS
    }
  }
}

union clause ast = CUnseal : (regidx, regidx, regidx)
function clause execute (CUnseal(cd, cs, ct)) =
{
  let cs_val = readCapReg(cs);
  let ct_val = readCapReg(ct);
  let ct_cursor = getCapCursor(ct_val);
  let (ct_base, ct_top) = getCapBounds(ct_val);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (ct_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, ct);
    RETIRE_FAIL
  } else if not (cs_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if ct_val.sealed then {
    handle_cheri_reg_exception(CapEx_SealViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor != unsigned(cs_val.otype) then {
    handle_cheri_reg_exception(CapEx_TypeViolation, ct);
    RETIRE_FAIL
  } else if not (ct_val.permit_unseal) then {
    handle_cheri_reg_exception(CapEx_PermitUnsealViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor < ct_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else if ct_cursor >= ct_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, ct);
    RETIRE_FAIL
  } else {
    writeCapReg(cd, {unsealCap(cs_val) with
      global=(cs_val.global & ct_val.global)
    });
    RETIRE_SUCCESS
  }
}

union clause ast = CCall : (regidx, regidx, regidx)
function clause execute (CCall(cs, cb, 0b00000)) = /* selector=0 */
{
  /* Partial implementation of CCall with checks in hardware, but raising a trap to perform trusted stack manipulation */
  let cs_val = readCapReg(cs);
  let cb_val = readCapReg(cb);
  let cs_cursor = getCapCursor(cs_val);
  let (cs_base, cs_top) = getCapBounds(cs_val);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if not (cs_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if cs_val.otype != cb_val.otype then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs);
    RETIRE_FAIL
  } else if not (cs_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs);
    RETIRE_FAIL
  } else if cb_val.permit_execute then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cb);
    RETIRE_FAIL
  } else if cs_cursor < cs_base then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs);
    RETIRE_FAIL
  } else if cs_cursor >= cs_top then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs);
    RETIRE_FAIL
  } else {
    handle_cheri_reg_exception(CapEx_CallTrap, cs);
    RETIRE_FAIL
  }
}

function clause execute (CCall(cs, cb, 0b00001)) = /* selector=1 */
{
  /* Jump-like implementation of CCall that unseals arguments */
  let cs_val = readCapReg(cs);
  let cb_val = readCapReg(cb);
  let newPC = [cs_val.address with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cs_val);
  if not (cs_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if not (cs_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if cs_val.otype != cb_val.otype then {
    handle_cheri_reg_exception(CapEx_TypeViolation, cs);
    RETIRE_FAIL
  } else if not (cs_val.permit_ccall) then {
    handle_cheri_reg_exception(CapEx_PermitCCallViolation, cs);
    RETIRE_FAIL
  } else if not (cb_val.permit_ccall) then {
    handle_cheri_reg_exception(CapEx_PermitCCallViolation, cb);
    RETIRE_FAIL
  } else if not (cs_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs);
    RETIRE_FAIL
  } else if cb_val.permit_execute then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cb);
    RETIRE_FAIL
  } else if not(inCapBounds(cs_val, newPC, min_instruction_bytes())) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cs);
    RETIRE_FAIL
  } else if newPCCBase[0] == bitone | (newPCCBase[1] == bitone & ~(haveRVC())) then {
    handle_cheri_reg_exception(CapEx_UnalignedBase, cb);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    writeCapReg(31, unsealCap(cb_val));
    nextPC = newPC;
    nextPCC = unsealCap(cs_val);
    RETIRE_SUCCESS
  }
}

function clause execute (CCall(_, _, 0b11111)) = /* CReturn */
{
  handle_cheri_reg_exception(CapEx_ReturnTrap, 0b11111); /* XXX what should correct reg number be? */
  RETIRE_FAIL
}

union clause ast = CJALR : (regidx, regidx)
function clause execute(CJALR(cd, cb)) =
{
  let cb_val = readCapReg(cb);
  let newPC = [cb_val.address with 0 = bitzero]; /* clear bit zero as for RISCV JALR */
  let newPCCBase = getCapBaseBits(cb_val);
  if not (cb_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cb);
    RETIRE_FAIL
  } else if (cb_val.sealed) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cb);
    RETIRE_FAIL
  } else if not (cb_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cb);
    RETIRE_FAIL
  } else if not(inCapBounds(cb_val, newPC, min_instruction_bytes())) then {
    handle_cheri_reg_exception(CapEx_LengthViolation, cb);
    RETIRE_FAIL
  } else if newPCCBase[0] == bitone | (newPCCBase[1] == bitone & ~(haveRVC())) then {
    handle_cheri_reg_exception(CapEx_UnalignedBase, cb);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instrucitons */
    assert(success, "Link cap should always be representable.");
    writeCapReg(cd, linkCap);
    nextPC  = newPC;
    nextPCC = cb_val;
    RETIRE_SUCCESS
  };
}

val handle_load_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, bool, word_width) -> Retired effect {escape, rmem, rreg, wmv, wmvt, wreg}
function handle_load_data_via_cap(rd, cs, cap_val, vaddrBits, is_unsigned, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  if not(cap_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if cap_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, cs);
    RETIRE_FAIL
  } else if not(inCapBounds(cap_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, cs);
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
function clause execute (CLoadDDC(rd, rs, is_unsigned, width)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs);
  handle_load_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, is_unsigned, width)
}

union clause ast = CLoadCap : (regidx, regidx, bool, word_width)
function clause execute (CLoadCap(rd, cs, is_unsigned, width)) =
{
  let cap_val = readCapReg(cs);
  let vaddr = cap_val.address;
  handle_load_data_via_cap(rd, 0b0 @ cs, cap_val, vaddr, is_unsigned, width)
}

val handle_load_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function handle_load_cap_via_cap(rd, cs, cap_val, vaddrBits) = {
  let aq : bool = false;
  let rl : bool = false;
  if not(cap_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if cap_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_load) then {
    handle_cheri_cap_exception(CapEx_PermitLoadViolation, cs);
    RETIRE_FAIL
  } else if not(inCapBounds(cap_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, cs);
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
                   else {v with tag = v.tag & cap_val.permit_load_cap};
          writeCapReg(rd, cr);
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = CLoadCapDDC : (regidx, regidx)
function clause execute (CLoadCapDDC(rd, rs)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs);
  handle_load_cap_via_cap(rd, DDC_IDX, ddc_val, vaddr)
}

union clause ast = CLoadCapCap : (regidx, regidx)
function clause execute (CLoadCapCap(rd, cs)) =
{
  let cap_val = readCapReg(cs);
  let vaddr = cap_val.address;
  handle_load_cap_via_cap(rd, 0b0 @ cs, cap_val, vaddr)
}

val handle_store_data_via_cap : (regidx, capreg_idx, Capability, xlenbits, word_width) -> Retired effect {eamem, escape, rmem, rreg, wmv, wmvt, wreg}
function handle_store_data_via_cap(rs, cs, cap_val, vaddrBits, width) = {
  let size = word_width_bytes(width);
  let aq : bool = false;
  let rl : bool = false;
  if not(cap_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if cap_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, cs);
    RETIRE_FAIL
  } else if not(inCapBounds(cap_val, vaddrBits, size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, cs);
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
          let rs_val = X(rs);
          let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
            (BYTE, _)     => mem_write_value(addr, 1, rs_val[7..0],  aq, rl, false),
            (HALF, _)     => mem_write_value(addr, 2, rs_val[15..0], aq, rl, false),
            (WORD, _)     => mem_write_value(addr, 4, rs_val[31..0], aq, rl, false),
            (DOUBLE, 64) => mem_write_value(addr, 8, rs_val,        aq, rl, false)
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
function clause execute (CStoreDDC(rd, rs, width)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs);
  handle_store_data_via_cap(rd, DDC_IDX, ddc_val, vaddr, width)
}

union clause ast = CStoreCap : (regidx, regidx, word_width)
function clause execute (CStoreCap(rs, cs, width)) =
{
  let cap_val = readCapReg(cs);
  let vaddr = cap_val.address;
  handle_store_data_via_cap(rs, 0b0 @ cs, cap_val, vaddr, width)
}

val handle_store_cap_via_cap : (regidx, capreg_idx, Capability, xlenbits) -> Retired effect {eamem, escape, rmem, rreg, wmv, wreg, wmvt}
function handle_store_cap_via_cap(rs, cs, cap_val, vaddrBits) = {
  let rs_val = readCapReg(rs);
  let aq : bool = false;
  let rl : bool = false;
  if not(cap_val.tag) then {
    handle_cheri_cap_exception(CapEx_TagViolation, cs);
    RETIRE_FAIL
  } else if cap_val.sealed then {
    handle_cheri_cap_exception(CapEx_SealViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_store) then {
    handle_cheri_cap_exception(CapEx_PermitStoreViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_store_cap) then {
    handle_cheri_cap_exception(CapEx_PermitStoreCapViolation, cs);
    RETIRE_FAIL
  } else if not (cap_val.permit_store_local_cap) & rs_val.tag & not(rs_val.global) then {
    handle_cheri_cap_exception(CapEx_PermitStoreLocalCapViolation, cs);
    RETIRE_FAIL
  } else if not(inCapBounds(cap_val, vaddrBits, cap_size)) then {
    handle_cheri_cap_exception(CapEx_LengthViolation, cs);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Write(Cap)) {
    TR_Failure(E_Extension(EXC_CHERI_VMEM_STORE_CAP), _) => {
      handle_cheri_cap_exception(CapEx_TLBNoStoreCap, cs);
      RETIRE_FAIL
    },
    TR_Failure(E_Extension(_), _) => { internal_error("unexpected cheri exception for cap store") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, aq, rl, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
        MemValue(_) => {
          let res : MemoryOpResult(bool) = mem_write_cap(addr, rs_val, aq, rl, false);
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
function clause execute (CStoreCapDDC(rd, rs)) =
{
  let ddc_val = DDC;
  let vaddr = ddc_val.address + X(rs);
  handle_store_cap_via_cap(rd, DDC_IDX, ddc_val, vaddr)
}

union clause ast = CStoreCapCap : (regidx, regidx)
function clause execute (CStoreCapCap(rs, cs)) =
{
  let cap_val = readCapReg(cs);
  let vaddr = cap_val.address;
  handle_store_cap_via_cap(rs, 0b0 @ cs, cap_val, vaddr)
}

union clause ast = CAP_AUIPC : (bits(20), regidx)
function clause execute CAP_AUIPC(imm, rd) = {
  let off : xlenbits = EXTS(imm @ 0x000);
  let ret = setCapAddrOrNull(PCC, PC + off);
  writeCapReg(rd, ret);
  RETIRE_SUCCESS
}

union clause ast = CLoadCapImm : (regidx, regidx, bits(12))
function clause execute CLoadCapImm(cd, rs1, off12) =
{
  let offset : xlenbits = EXTS(off12);
  let (cap_val, vaddr, cause_regno) = get_cheri_cap_addr(rs1, offset);
  handle_load_cap_via_cap(cd, cause_regno, cap_val, vaddr)
}

union clause ast = CStoreCapImm : (regidx, regidx, bits(12))
function clause execute CStoreCapImm(cs2, rs1, off12) =
{
  let offset : xlenbits = EXTS(off12);
  let (cap_val, vaddr, cause_regno) = get_cheri_cap_addr(rs1, offset);
  handle_store_cap_via_cap(cs2, cause_regno, cap_val, vaddr)
}

/*
NB: Must be careful about order of matching because unused register
fields are re-used as additional function codes: more specific matches
must come before more general ones. In our case that means two-arg
instructions (that have 0x7f in func7 field) must come before
three-arg ones.
*/

/* Two arg */

mapping clause encdec = CGetPerm(rd, cb)   if (haveXcheri()) <-> 0b1111111 @ 0b00000 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetType(rd, cb)   if (haveXcheri()) <-> 0b1111111 @ 0b00001 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetBase(rd, cb)   if (haveXcheri()) <-> 0b1111111 @ 0b00010 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetLen(rd, cb)    if (haveXcheri()) <-> 0b1111111 @ 0b00011 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetTag(rd, cb)    if (haveXcheri()) <-> 0b1111111 @ 0b00100 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetSealed(rd, cb) if (haveXcheri()) <-> 0b1111111 @ 0b00101 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetOffset(rd, cb) if (haveXcheri()) <-> 0b1111111 @ 0b00110 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetFlags(rd, cb)  if (haveXcheri()) <-> 0b1111111 @ 0b00111 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetAddr(rd, cb)   if (haveXcheri()) <-> 0b1111111 @ 0b01111 @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CMove(cd, cs)      if (haveXcheri()) <-> 0b1111111 @ 0b01010 @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CClearTag(cd, cs)  if (haveXcheri()) <-> 0b1111111 @ 0b01011 @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CJALR(cd, cb)      if (haveXcheri()) <-> 0b1111111 @ 0b01100 @ cb @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CCheckPerm(cs, rt) if (haveXcheri()) <-> 0b1111111 @ 0b01000 @ rt @ 0b000 @ cs @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCheckType(cs, cb) if (haveXcheri()) <-> 0b1111111 @ 0b01001 @ cb @ 0b000 @ cs @ 0b1011011 if (haveXcheri())

mapping clause encdec = ClearRegs(GPRegs, q, m3 @ m5) if (haveXcheri()) <-> 0b1111111 @ 0b01101 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri())
mapping clause encdec = ClearRegs(FPRegs, q, m3 @ m5) if (haveXcheri()) <-> 0b1111111 @ 0b10000 @ q : bits(2) @ m3 : bits(3) @ 0b000 @ m5 : regidx @ 0b1011011 if (haveXcheri())

mapping clause assembly = CGetPerm(rd, cb)   <-> "CGetPerm"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetFlags(rd, cb)  <-> "CGetFlags"  ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetType(rd, cb)   <-> "CGetType"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetBase(rd, cb)   <-> "CGetBase"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetLen(rd, cb)    <-> "CGetLen"    ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetTag(rd, cb)    <-> "CGetTag"    ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetSealed(rd, cb) <-> "CGetSealed" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetOffset(rd, cb) <-> "CGetOffset" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)
mapping clause assembly = CGetAddr(rd, cb)   <-> "CGetAddr"   ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb)

mapping clause assembly = CMove(cd, cs)      <-> "CMove"      ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs)
mapping clause assembly = CClearTag(cd, cs)  <-> "CClearTag"  ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs)
mapping clause assembly = CJALR(0b00000, cb) <-> "CJR"        ^ spc() ^ reg_name(cb)
mapping clause assembly = CJALR(cd, cb)      <-> "CJALR"      ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb)

mapping clause assembly = CCheckPerm(cs, rt) <-> "CCheckPerm" ^ spc() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CCheckType(cs, cb) <-> "CCheckType" ^ spc() ^ reg_name(cs) ^ sep() ^ reg_name(cb)

mapping clause assembly = ClearRegs(GPRegs, q, m8) <-> "Clearq"   ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)
mapping clause assembly = ClearRegs(FPRegs, q, m8) <-> "FPClearq" ^ spc() ^ hex_bits_2(q) ^ sep() ^ hex_bits_8(m8)

/* Three arg */

mapping clause encdec = CSeal(cd, cs, ct)       if (haveXcheri()) <-> 0b0001011 @ ct @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CUnseal(cd, cs, ct)     if (haveXcheri()) <-> 0b0001100 @ ct @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CAndPerm(cd, cs, rt)    if (haveXcheri()) <-> 0b0001101 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetFlags(cd, cs, rt)   if (haveXcheri()) <-> 0b0001110 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetOffset(cd, cs, rt)  if (haveXcheri()) <-> 0b0001111 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetAddr(cd, cs, rt)    if (haveXcheri()) <-> 0b0010000 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CIncOffset(cd, cs, rt)  if (haveXcheri()) <-> 0b0010001 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBounds(cd, cs, rt)  if (haveXcheri()) <-> 0b0001000 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsExact(cd, cs, rt) if (haveXcheri()) <-> 0b0001001 @ rt @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CBuildCap(cd, cb, ct)   if (haveXcheri()) <-> 0b0011101 @ ct @ cb @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCopyType(cd, cb, ct)   if (haveXcheri()) <-> 0b0011110 @ ct @ cb @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCSeal(cd, cs, ct)      if (haveXcheri()) <-> 0b0011111 @ ct @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CToPtr(rd, cb, cs)      if (haveXcheri()) <-> 0b0010010 @ cs @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CFromPtr(cd, cb, rs)    if (haveXcheri()) <-> 0b0010011 @ rs @ cb @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSub(rd, cb, ct)        if (haveXcheri()) <-> 0b0010100 @ ct @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CCall(cs, cb, 0b00000)  if (haveXcheri()) <-> 0b1111110 @ cb @ cs @ 0b000 @ 0b00000 @ 0b1011011 /* CCall */ if (haveXcheri())
mapping clause encdec = CCall(cs, cb, 0b00001)  if (haveXcheri()) <-> 0b1111110 @ cb @ cs @ 0b000 @ 0b00001 @ 0b1011011 /* CCallFast */ if (haveXcheri())
mapping clause encdec = CCall(cs, cb, 0b11111)  if (haveXcheri()) <-> 0b1111110 @ cb @ cs @ 0b000 @ 0b11111 @ 0b1011011 /* CReturn */ if (haveXcheri())

mapping clause encdec = CTestSubset(rd, cb, ct) if (haveXcheri()) <-> 0b0100000 @ ct @ cb @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSpecialRW(cd, cs, idx) if (haveXcheri()) <-> 0b0000001 @ idx @ cs @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CIncOffsetImmediate(cd, cb, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cb @ 0b001 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsImmediate(cd, cb, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cb @ 0b010 @ cd @ 0b1011011 if (haveXcheri())

mapping clause assembly = CSeal(cd, cs, ct)      <-> "CSeal"      ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(ct)
mapping clause assembly = CUnseal(cd, cs, ct)    <-> "CUnseal"    ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(ct)
mapping clause assembly = CAndPerm(cd, cs, rt)   <-> "CAndPerm"   ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CSetFlags(cd, cs, rt)  <-> "CSetFlags"  ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CSetOffset(cd, cs, rt) <-> "CSetOffset" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CSetAddr(cd, cs, rt)   <-> "CSetAddr"   ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CIncOffset(cd, cs, rt) <-> "CIncOffset" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CSetBounds(cd, cs, rt) <-> "CSetBounds" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CSetBoundsExact(cd, cs, rt) <-> "CSetBoundsExact" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(rt)
mapping clause assembly = CBuildCap(cd, cb, ct) <-> "CBuildCap"   ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(ct)
mapping clause assembly = CCopyType(cd, cb, ct) <-> "CCopyType"   ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(ct)
mapping clause assembly = CCSeal(cd, cs, ct)    <-> "CCSeal"      ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ reg_name(ct)

mapping clause assembly = CToPtr(rd, cb, cs)    <-> "CToPtr"      ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(cs)
mapping clause assembly = CFromPtr(cd, cb, rs)  <-> "CFromPtr"    ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(rs)
mapping clause assembly = CSub(rd, cb, ct)      <-> "CSub"        ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(ct)
mapping clause assembly = CCall(cs, cb, 0b00000) <-> "CCall"      ^ spc() ^ reg_name(cs) ^ sep() ^ reg_name(cb)
mapping clause assembly = CCall(cs, cb, 0b00001) <-> "CCallFast"  ^ spc() ^ reg_name(cs) ^ sep() ^ reg_name(cb)
mapping clause assembly = CCall(cs, cb, 0b11111) <-> "CCallReturn" ^ spc() ^ reg_name(cs) ^ sep() ^ reg_name(cb)

mapping clause assembly = CTestSubset(rd, cb, ct) <-> "CTestSubset" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cb) ^ sep() ^ reg_name(ct)
mapping clause assembly = CSpecialRW(cd, cs, idx) <-> "CSpecialRW"  ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cs) ^ sep() ^ hex_bits_5(idx)

mapping clause assembly = CIncOffsetImmediate(cd, cb, imm12) <-> "CIncOffsetImmediate" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb) ^ sep() ^ hex_bits_12(imm12)
mapping clause assembly = CSetBoundsImmediate(cd, cb, imm12) <-> "CSetBoundsImmediate" ^ spc() ^ reg_name(cd) ^ sep() ^ reg_name(cb) ^ sep() ^ hex_bits_12(imm12)

/* Loads and stores */

let haveRV128 = sizeof(xlen) >= 128
let haveRV64  = sizeof(xlen) >= 64

mapping clause encdec = CLoadDDC(rd, rs, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b00000 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbddc */
mapping clause encdec = CLoadDDC(rd, rs, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b00001 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhddc */
mapping clause encdec = CLoadDDC(rd, rs, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b00010 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lwddc */
mapping clause encdec = CLoadDDC(rd, rs, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b00011 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64) /* ldddc */
mapping clause encdec = CLoadDDC(rd, rs, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b00100 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbuddc */
mapping clause encdec = CLoadDDC(rd, rs, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b00101 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhuddc */
mapping clause encdec = CLoadDDC(rd, rs, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b00110 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwuddc */
mapping clause encdec = CLoadDDC(rd, rs, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b00111 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* lduddc */
mapping clause encdec = CLoadCapDDC(rd, rs)             if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b10111 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lqddc */
mapping clause encdec = CLoadCapDDC(rd, rs)             if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b00011 @ rs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* ldddc */

mapping clause encdec = CLoadCap(rd, cs, false, BYTE)   if (haveXcheri()) <-> 0b1111101 @ 0b01000 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbcap */
mapping clause encdec = CLoadCap(rd, cs, false, HALF)   if (haveXcheri()) <-> 0b1111101 @ 0b01001 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhcap */
mapping clause encdec = CLoadCap(rd, cs, false, WORD)   if (haveXcheri()) <-> 0b1111101 @ 0b01010 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lwcap */
mapping clause encdec = CLoadCap(rd, cs, false, DOUBLE) if (haveXcheri() & haveRV64) <-> 0b1111101 @ 0b01011 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* ldcap */
mapping clause encdec = CLoadCap(rd, cs, true, BYTE)    if (haveXcheri()) <-> 0b1111101 @ 0b01100 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lbucap */
mapping clause encdec = CLoadCap(rd, cs, true, HALF)    if (haveXcheri()) <-> 0b1111101 @ 0b01101 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri())  /* lhucap */
mapping clause encdec = CLoadCap(rd, cs, true, WORD)    if (haveXcheri() & haveRV64)  <-> 0b1111101 @ 0b01110 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV64)  /* lwucap */
mapping clause encdec = CLoadCap(rd, cs, true, DOUBLE)  if (haveXcheri() & haveRV128) <-> 0b1111101 @ 0b01111 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & haveRV128) /* lducap */
mapping clause encdec = CLoadCapCap(rd, cs)             if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111101 @ 0b11111 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64)  /* lqcap */
mapping clause encdec = CLoadCapCap(rd, cs)             if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111101 @ 0b01011 @ cs @ 0b000 @ rd @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32)  /* ldcap */

mapping clause encdec = CStoreDDC(rs2, rs1, BYTE)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00000 @ 0b1011011 if (haveXcheri()) /* sbddc */
mapping clause encdec = CStoreDDC(rs2, rs1, HALF)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00001 @ 0b1011011 if (haveXcheri()) /* shddc */
mapping clause encdec = CStoreDDC(rs2, rs1, WORD)       if (haveXcheri()) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00010 @ 0b1011011 if (haveXcheri()) /* swddc */
mapping clause encdec = CStoreDDC(rs2, rs1, DOUBLE)     if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sdddc */
mapping clause encdec = CStoreCapDDC(rs2, rs1)          if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sqddc */
mapping clause encdec = CStoreCapDDC(rs2, rs1)          if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ rs2 @ rs1 @ 0b000 @ 0b00011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sdddc */

mapping clause encdec = CStoreCap(rs2, cs, BYTE)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01000 @ 0b1011011 if (haveXcheri()) /* sbcap */
mapping clause encdec = CStoreCap(rs2, cs, HALF)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01001 @ 0b1011011 if (haveXcheri()) /* shcap */
mapping clause encdec = CStoreCap(rs2, cs, WORD)        if (haveXcheri()) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01010 @ 0b1011011 if (haveXcheri()) /* swcap */
mapping clause encdec = CStoreCap(rs2, cs, DOUBLE)      if (haveXcheri() & haveRV64) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & haveRV64) /* sdcap */
mapping clause encdec = CStoreCapCap(rs2, cs)           if (haveXcheri() & sizeof(xlen) == 64) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01100 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 64) /* sqcap */
mapping clause encdec = CStoreCapCap(rs2, cs)           if (haveXcheri() & sizeof(xlen) == 32) <-> 0b1111100 @ rs2 @ cs  @ 0b000 @ 0b01011 @ 0b1011011 if (haveXcheri() & sizeof(xlen) == 32) /* sdcap */

mapping clause assembly = CLoadDDC(rd, rs, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ "DDC" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs)
mapping clause assembly = CLoadCap(rd, cs, u, w) <-> "l" ^ size_mnemonic(w) ^ maybe_u(u) ^ "Cap" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(cs)
mapping clause assembly = CStoreDDC(rd, rs, w)   <-> "s" ^ size_mnemonic(w) ^ "DDC" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs)
mapping clause assembly = CStoreCap(rd, rs, w)   <-> "s" ^ size_mnemonic(w) ^ "Cap" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs)
mapping clause assembly = CLoadCapDDC(rd, rs)    <-> "lqDDC" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs)
mapping clause assembly = CLoadCapCap(rd, rs)    <-> "lqCap" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs)
mapping clause assembly = CStoreCapDDC(rs2, rs1) <-> "sqDDC" ^ spc() ^ reg_name(rs2) ^ sep() ^ reg_name(rs1)
mapping clause assembly = CStoreCapCap(rs2, rs1) <-> "sqCap" ^ spc() ^ reg_name(rs2) ^ sep() ^ reg_name(rs1)

mapping clause encdec = CLoadCapImm(cd, rs1, offset) if sizeof(xlen) == 64 <-> offset @ rs1 @ 0b010 @ cd @ 0b0001111 if sizeof(xlen) == 64 /* clc / lq */
mapping clause encdec = CLoadCapImm(cd, rs1, offset) if sizeof(xlen) == 32 <-> offset @ rs1 @ 0b011 @ cd @ 0b0000011 if sizeof(xlen) == 32 /* clc / ld */

mapping clause encdec = CStoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 64 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b100 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 64 /* csc / sq */
mapping clause encdec = CStoreCapImm(cs2, rs1, off7 @ off5) if sizeof(xlen) == 32 <-> off7 : bits(7) @ cs2 @ rs1 @ 0b011 @ off5 : bits(5) @ 0b0100011 if sizeof(xlen) == 32 /* csc / sd */

mapping clause assembly = CLoadCapImm(cd, rs1, offset)   <-> "clc" ^ spc() ^ reg_name(cd) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = CStoreCapImm(cs2, rs1, offset) <-> "csc" ^ spc() ^ reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
