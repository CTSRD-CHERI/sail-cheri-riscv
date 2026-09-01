function test_cheri_cap_encoding() -> unit = {
    // Check the null cap decodes from all 0s.
    // In future we will encode it from all 0s so we won't need to check that.
    assert(bitsToCap(false, zeros()) == null_cap, "zeros don't decode to null capability");
    assert(capToMetadataBits(null_cap).bits == zeros(), "null capability doesn't encode to zeros");
}

function test_cheri_yamask() -> unit = {
    // Check the mask for 0 length is all ones.
    assert(getRepresentableAlignmentMask(zeros()) == ones());
}

function test_cheri_fault() -> unit = {
    // Check that CHERI exceptions are reported with their code
    PCC = {setCapMode(PCC, CapPtrMode)};
    assert(execute(LoadCapImm(zreg, zreg, zeros())) == RETIRE_FAIL); // Throw tag exception
    assert(mcause[Cause] == zero_extend(ext_exc_type_to_bits(EXC_CHERI(CapCheckType_Ld()))));
    assert(execute(StoreCapImm(zreg, zreg, zeros())) == RETIRE_FAIL); // Throw tag exception
    assert(mcause[Cause] == zero_extend(ext_exc_type_to_bits(EXC_CHERI(CapCheckType_St()))));
    // TODO test PTE exceptions
}

function assert_illegal_cause() -> unit = {
    assert(mcause[Cause] == zero_extend(exceptionType_to_bits(E_Illegal_Instr())))
}

function try_system_insts(pccCap : Capability, allowed : bool) -> unit = {
    let expected = if allowed then RETIRE_SUCCESS else RETIRE_FAIL;
    PCC = pccCap;
    set_cur_privilege(Machine);
    assert(execute(MRET()) == expected);
    if not(allowed) then assert_illegal_cause();
    PCC = pccCap;
    set_cur_privilege(Machine);
    assert(execute(SRET()) == expected);
    if not(allowed) then assert_illegal_cause();
    if extensionEnabled(Ext_Zicbom) then {
        PCC = pccCap;
        set_cur_privilege(Machine);
        assert(execute(RISCV_ZICBOM(CBO_INVAL, Regidx(0b00000))) == expected);
        if not(allowed) then assert_illegal_cause();
    }
}

function test_cheri_system_faults() -> unit = {
    ddc_y = root_cap;
    try_system_insts(root_cap, true);
    try_system_insts(setArchPerms(root_cap, {getArchPermsLegalized(root_cap) with ASR=false}), false);
}

//function test_cheri_sdtrig() -> unit = {
//  set_cur_privilege(Machine);
//  assert (not(debug_mode_active));
//  let addr : xlenbits = zero_extend(0x01234567);
//  let src : regidx = Regidx(0b00100);
//  let rd : regidx = Regidx(0b00011);
//  Y(src) = { null_cap with address = addr };
//  PCC = setCapMode(PCC, CapPtrMode);
//  let ret = execute(LoadCapImm(rd, src, zeros()));
//  assert (ret == RETIRE_FAIL);
//  assert (mcause[Cause] == zero_extend (0x1C));
//  assert (not(debug_mode_active));
//  let tdata1 : xlenbits = 0x68 @ zeros(xlen - 24) @ 0x107f;
//  write_tdata1_underlying(0, tdata1);
//  write_tdata2_underlying(0, addr);
//  PCC = setCapMode(PCC, CapPtrMode);
//  let ret = execute(LoadCapImm(rd, src, zeros()));
//  assert (ret == RETIRE_DEBUG_TRIGGER);
//  assert (debug_mode_active);
//  let _ = execute (DRET());
//  assert (not(debug_mode_active));
//  X(src) = addr;
//  set_ddc_y(null_cap);
//  PCC = setCapMode(PCC, IntPtrMode);
//  let _ = execute(LOAD(zeros(), src, rd, true, BYTE, false, false));
//  assert (ret == RETIRE_DEBUG_TRIGGER);
//  assert (debug_mode_active);
//}

function test_cheri_nofastrep () -> unit = {
    // Check that the representability check is exact, i.e. that the historical
    // "fast representability check" is not in use.
    let capR : regidx = Regidx(0b00001);
    let addrR : regidx = Regidx(0b00010);
    let outR : regidx = Regidx(0b00011);
    // Fields for a capability with its address very close to the top of the
    // representable region. The representable region has approximately half
    // the object's size above the object and below.
    let base : CapAddrBits = zero_extend(0x800_0000);
    let top : CapLenBits = zero_extend(0x8f0_0000);
    let addr : CapAddrBits = zero_extend(0x97f_fffe);
    // An increment that still leaves the capability within representable
    // bounds. However, the fast representability check would conservatively
    // assume that addr+inc would carry, which would put the address outside
    // the representable range.
    let increment : bits(12) = zero_extend(0x1);
    // Construct the cap
    let (exact, cap) = setCapBounds({root_cap with address = base}, base, top);
    assert(exact);
    Y(capR) = cap;
    X(addrR) = addr;
    assert(execute(YADDRW(capR, capR, addrR)) == RETIRE_SUCCESS);
    assert(Y(capR).tag);
    // Perform the YADDI that would detag the capability if the fast
    // representability check is being used.
    assert(execute(YADDI(outR, capR, increment)) == RETIRE_SUCCESS);
    assert(Y(outR).tag);
    // Check that incrementing by one more does in fact detag the
    // cap, i.e. that if the fast representability check's assumption
    // of a carry were accurate, then the capability should be
    // detagged.
    assert(execute(YADDI(outR, capR, increment+1)) == RETIRE_SUCCESS);
    assert(not(Y(outR).tag));
}

val test_cheri_zba_mode : (bitvector(32), regidx, bool) -> unit
function test_cheri_zba_mode(instBits, resR, isCap) = {
    // Check that integer mode uses integer instructions
    PCC = {setCapMode(PCC, IntPtrMode)};
    let ast = ext_decode(instBits);
    assert(execute(ast) == RETIRE_SUCCESS);
    assert(Y(resR).tag == isCap);
    // Check that cap mode doesn't change the decoding (it did in previous spec!)
    PCC = {setCapMode(PCC, CapPtrMode)};
    let ast = ext_decode(instBits);
    assert(execute(ast) == RETIRE_SUCCESS);
    assert(Y(resR).tag == isCap)
}

function test_cheri_zba() -> unit = {
    let capR : regidx = Regidx(0b00001);
    let indR : regidx = Regidx(0b00010);
    let resR : regidx = Regidx(0b00011);
    Y(capR) = root_cap;
    X(indR) = to_bits(xlen, 1);
    Y(resR) = root_cap;
    // Test integer versions of instructions
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH1ADD)), resR, false);
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH2ADD)), resR, false);
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH3ADD)), resR, false);
    if xlen == 32 then () else {
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_ADDUW)), resR, false);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH1ADDUW)), resR, false);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH2ADDUW)), resR, false);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH3ADDUW)), resR, false);
    };
    // Test CHERI versions of instructions
    test_cheri_zba_mode(encdec(ZBA_Y_RTYPE(capR, indR, resR, RISCV_YSH1ADD)), resR, true);
    test_cheri_zba_mode(encdec(ZBA_Y_RTYPE(capR, indR, resR, RISCV_YSH2ADD)), resR, true);
    test_cheri_zba_mode(encdec(ZBA_Y_RTYPE(capR, indR, resR, RISCV_YSH3ADD)), resR, true);
    if xlen == 32 then () else {
        test_cheri_zba_mode(encdec(ZBA_Y_RTYPEUW(capR, indR, resR, RISCV_YSH1ADDUW)), resR, true);
        test_cheri_zba_mode(encdec(ZBA_Y_RTYPEUW(capR, indR, resR, RISCV_YSH2ADDUW)), resR, true);
        test_cheri_zba_mode(encdec(ZBA_Y_RTYPEUW(capR, indR, resR, RISCV_YSH3ADDUW)), resR, true);
        test_cheri_zba_mode(encdec(ZBA_Y_RTYPEUW(capR, indR, resR, RISCV_YSH4ADDUW)), resR, true);
        test_cheri_zba_mode(encdec(ZBA_Y_RTYPE(capR, indR, resR, RISCV_YSH4ADD)), resR, true);
    }
}

// Verify that setting the bounds on Y(capR) based on Y(capR) and X(lenR)
// gives the expected result.
function check_format(
    capR : regidx,
    lenR : regidx,
    dstR : regidx,
    aimE : CapExponent,
    aimIE : bool,
    aimLen : CapLenBits,
) -> unit = {
    assert(execute(YBNDSW(dstR, capR, lenR)) == RETIRE_SUCCESS);
    assert(Y(dstR).internal_exponent == aimIE);
    assert(Y(dstR).E == aimE);
    assert(to_bits(cap_len_width, getCapLength(Y(dstR))) == aimLen);
}

function test_cheri_l8() -> unit = {
    if (xlen != 32) then return ();
    let capR : regidx = Regidx(0b00001);
    let lenR : regidx = Regidx(0b00010);
    let dstR : regidx = Regidx(0b00011);
    Y(capR) = root_cap;
    let impliedLen  = 0b00_1111_1111;
    X(lenR) = zero_extend(impliedLen);
    check_format(capR, lenR, dstR, 0, false, zero_extend(impliedLen));
    let l8LoLen     = 0b01_0000_0000;
    X(lenR) = zero_extend(l8LoLen);
    check_format(capR, lenR, dstR, 0, false, zero_extend(l8LoLen));
    let l8HiLen     = 0b01_1111_1111;
    X(lenR) = zero_extend(l8HiLen);
    check_format(capR, lenR, dstR, 0, false, zero_extend(l8HiLen));
    let internalLen = 0b10_0000_0000;
    X(lenR) = zero_extend(internalLen);
    check_format(capR, lenR, dstR, 1, true, zero_extend(internalLen));
}

// The sail Capability datatype allows capabilities that could never actually
// be encoded. This function will return false given these.
function encodable(c : Capability) -> bool =
    bitsToCap(c.tag, capToMetadataBits(c).bits @ c.address) == c

function test_cheri_redundant() -> unit = {
    // Construct capabilities that are redundant with the L8 bit:
    // an internal exponent loses the bottom bits of B and T to encode the exponent,
    // L8 keeps those bits by setting L8 to 1 and maintaining an implied exponent
    let badCap =
      {
         root_cap with
         E = 0,
         B = zeros(),
         T = 0b01 @ zeros(cap_mantissa_width - 2),
         internal_exponent = true,
      };
    let goodCap =
      {
         root_cap with
         E = 0,
         B = zeros(),
         T = 0b01 @ zeros(cap_mantissa_width - 2),
         internal_exponent = false,
      };
    // Properties we want:
    // We allow exactly one of the caps
    assert((encodable(goodCap) & not(boundsMalformed(goodCap))) ==
        not(encodable(badCap ) & not(boundsMalformed(badCap))));
    // If we can have the good cap then we get the good cap
    if (encodable(goodCap)) then assert(not(boundsMalformed(goodCap)));

    // Properties we expect:
    // We get the goodCap on RV32
    if xlen == 32 then assert(not(boundsMalformed(goodCap)));
    // We get the badCap on RV64
    if xlen == 64 then assert(not(boundsMalformed(badCap)));
}

function test_cheri_rounding() -> unit = {
    let capR : regidx = Regidx(0b00001);
    let lenR : regidx = Regidx(0b00010);
    let outR : regidx = Regidx(0b00011);
    Y(capR) = {root_cap with address = to_bits(xlen, 1)};
    X(lenR) = 0b1 @ ones(sizeof(xlen - 2)) @ 0b1; // very unaligned
    // Check that YBNDSW is exact
    let _ = execute(YBNDSW(outR, capR, lenR));
    assert(not(Y(outR).tag));
    // Check that YBNDSRW rounds
    let _ = execute(YBNDSRW(outR, capR, lenR));
    assert(Y(outR).tag);
    // Check that YBNDSWI doesn't assert with max requested len
    let _ = execute(YBNDSWI(outR, capR, ones()));
    assert(Y(outR).tag);
    let _ = execute(YBNDSWI(outR, capR, ones()));
    assert(Y(outR).tag);
}

function test_cheri_permission_encoding() -> unit = {
    // Verify that YMODEW doesn't affect other permissions bits even if they have
    // malformed permissions.
    let capR : regidx = Regidx(0b00001);
    let modeR : regidx = Regidx(0b00010);
    let dstR : regidx = Regidx(0b00011);
    if cap_size == 16 then {
        // Malformed permission combination, but it can be encoded (though is reserved) on RV64.
        // M=1 (IntPtrMode), LM=0, SL=0, EL=0 ASR=1, X=0, R=1, W=1, C=0
        let invalid = {null_cap with ap_m = 0b100010110};
        // We shouldn't be able to change the mode to CapPtrMode because X=0
        // so this should have no effect.
        Y(capR) = invalid;
        X(modeR) = zero_extend(execution_mode_encdec(CapPtrMode));
        assert(execute(YMODEW(dstR, capR, modeR)) == RETIRE_SUCCESS);
        assert(Y(dstR) == invalid)
    };

    // Test that clearing the X permission of a capability with M=1 (IntPtrMode)
    // clears M (CapPtrMode).
    let intmode_inf = setCapMode(root_cap, IntPtrMode);
    assert(getCapMode(intmode_inf) == IntPtrMode);
    let all_perms_but_x = {getArchPermsLegalized(intmode_inf) with X=false};
    let cap_x_cleared = setArchPerms(intmode_inf, all_perms_but_x);
    assert(getCapMode(cap_x_cleared) == CapPtrMode);
}

function test_cheri_circular() -> unit = {
    let capR : regidx = Regidx(0b00001);
    let valR : regidx = Regidx(0b00010);
    PCC = {setCapMode(PCC, CapPtrMode)};

    // Install all-permissive PMA so we're allowed to touch weird addresses.
    let attr : PMA = struct {
      cacheable                        = true,
      coherent                         = true,
      executable                       = true,
      readable                         = true,
      writable                         = true,
      readIdempotent                   = true,
      writeIdempotent                  = true,
      relaxed                          = true,
      misalignmentCausesAccessFault    = false,
      misalignmentCausesAlignmentFault = false,
      atomicSupport                    = AMONone,
      reservability                    = RsrvNone,
      taggable                         = true,
      taggableAccessFaults             = false,
      supportsCboZero                  = true,
    };
    // Since PMAs can't encode a 2^XLEN region we'll just have two regions.
    let half_mem = 0b1 @ zeros(physaddrbits_len - 1);
    let region_0 : PMA_Region = struct {
      base       = physaddr(zeros()),
      size       = half_mem,
      attributes = attr,
    };
    let region_1 : PMA_Region = struct {
      base       = physaddr(half_mem),
      size       = half_mem,
      attributes = attr,
    };
    pma_regions = [| region_0, region_1 |];

    // Write to low end of address space
    X(valR) = zeros(sizeof(xlen - 8)) @ 0xbe;
    Y(capR) = { root_cap with address = to_bits(xlen, 0) };
    assert(execute(STORE(zeros(), valR, capR, BYTE, false, false)) == RETIRE_SUCCESS);
    // Write to high end of address space
    X(valR) = zeros(sizeof(xlen - 8)) @ 0xef;
    Y(capR) = { root_cap with address = to_bits(xlen, -1) };
    assert(execute(STORE(zeros(), valR, capR, BYTE, false, false)) == RETIRE_SUCCESS);
    // Perform wrapping read
    assert(execute(LOAD(zeros(), capR, valR, true, HALF, false, false)) == RETIRE_SUCCESS);
    // Check we got the right answer
    assert(X(valR) == zeros(sizeof(xlen - 16)) @ 0xbeef);

    // Create a capability that has top > "max top" and nonzero base
    // Then do a load wrapping the top address and check it gives a bounds violation
    let top = 0b1 @ zeros(sizeof(xlen)) + zero_extend(0x1000);
    let base = ones(sizeof(xlen)) - zero_extend(0x1000);
    let (_, capTest) = setCapBounds(root_cap, base, top);
    Y(capR) = { capTest with address = ones(sizeof(xlen)) };
    assert(execute(LOAD(zeros(), capR, valR, true, HALF, false, false)) == RETIRE_FAIL);
    assert(mcause[Cause] == zero_extend(ext_exc_type_to_bits(EXC_CHERI(CapCheckType_Ld()))));
}

function test_cheri_ylen_csr() -> unit = {
    let csr : csreg = csr_name_map("mscratch");
    let (_, capTest) = setCapBounds(root_cap, zero_extend(0x00010000), zero_extend(0x00020000));
    let src : regidx = Regidx(0b00100);
    let dst : regidx = Regidx(0b00101);
    let tmp : regidx = Regidx(0b11000);
    Y(src) = capTest;
    // ///////////////////////////////////////////
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, true, false);
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(Y(src) == Y(dst));
    assert(Y(dst) == capTest);
    // ///////////////////////////////////////////
    let addr : xlenbits = zero_extend(0x00010111);
    X(tmp) = addr;
    PCC = {setCapMode(PCC, IntPtrMode)};
    let _ = handle_csr_op(csr, tmp, dst, false, CSRRW, true, false);
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(Y(dst) == {capTest with address = addr});
    let addr2 : xlenbits = zero_extend(0x00070111);
    X(tmp) = addr2;
    PCC = {setCapMode(PCC, IntPtrMode)};
    let _ = handle_csr_op(csr, tmp, dst, false, CSRRW, true, false);
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(Y(dst) == {capTest with address = addr2, tag = false});
}

function attempt_csr_access(priv : Privilege, asr : bool, op : csrop, csr : csreg, src : regidx, dst : regidx) -> Retired = {
    set_cur_privilege(priv);
    PCC = setArchPerms(PCC, {getArchPermsLegalized(PCC) with ASR=asr});
    execute(CSR(csr, src, dst, false, op))
}

function test_csr_access_priv_asr_rw(csr : string, priv : Privilege, asr : bool, write : bool, allowed : bool) -> unit = {
    Y(Regidx(0b00001)) = root_cap;
    let src = if write then Regidx(0b00001) else zreg;
    let dst = if write then zreg else Regidx(0b00001);
    let op = if write then CSRRW else CSRRS;
    let ret = attempt_csr_access(priv, asr, op, csr_name_map(csr), src, dst);
    assert(ret == (if allowed then RETIRE_SUCCESS else RETIRE_FAIL))
}

function test_csr_access_priv_asr(csr : string, priv : Privilege, asr : bool, allowed : bool, ro : bool) -> unit = {
    test_csr_access_priv_asr_rw(csr, priv, asr, false, allowed);
    test_csr_access_priv_asr_rw(csr, priv, asr, true, allowed & not(ro));
}

function test_csr_access_priv(csr : string, priv : Privilege, allowed : bool, needsAsrWrite : bool, needsAsrRead : bool, ro : bool) -> unit = {
    test_csr_access_priv_asr(csr, priv, true, allowed, ro);
    test_csr_access_priv_asr(csr, priv, false, allowed & not(needsAsrRead), ro | needsAsrWrite);
}

function test_csr_access(csr : string, minPriv : Privilege, ro: bool, needsAsrWrite : bool, needsAsrRead : bool) -> unit = {
    test_csr_access_priv(csr, Machine, true, needsAsrWrite, needsAsrRead, ro);
    test_csr_access_priv(csr, Supervisor, minPriv == Supervisor | minPriv == User, needsAsrWrite, needsAsrRead, ro);
    test_csr_access_priv(csr, User, minPriv == User, needsAsrWrite, needsAsrRead, ro);
}

function test_cheri_csr_access_control() -> unit = {
    debug_mode_active = false;
    // Turn on all counters
    mcounteren = struct { bits = ones() };
    scounteren = struct { bits = ones() };
    //              CSR        , minPriv   , ro   , needsAsrWrite, needsAsrRead
    // Completely new registers added by CHERI
    test_csr_access("ddc"      , User      , false, false, false);
    test_csr_access("mtid"     , Machine   , false, true , false);
    test_csr_access("stid"     , Supervisor, false, true , false);
    test_csr_access("utid"     , User      , false, true , false);
    // Some exception-related registers
    test_csr_access("mtvec"    , Machine   , false, true , true);
    test_csr_access("mepc"     , Machine   , false, true , true);
    test_csr_access("mtval"    , Machine   , false, true , true);
    test_csr_access("mscratch" , Machine   , false, true , true);
    test_csr_access("stvec"    , Supervisor, false, true , true);
    test_csr_access("sepc"     , Supervisor, false, true , true);
    test_csr_access("stval"    , Supervisor, false, true , true);
    test_csr_access("sscratch" , Supervisor, false, true , true);
    // Unprivileged registers
    test_csr_access("cycle"    , User      , true , false, false);
    test_csr_access("instret"  , User      , true , false, false);
}

function assert_behaviour(inCap : Capability,
                          capR : regidx,
                          outR : regidx,
                          instruction : ast,
                          exc : option(CapCheckType),
                          outIsCap : bool,
                          outCap : Capability,
                          outBits : xlenbits) -> unit = {
    Y(capR) = inCap;
    assert(Y(capR).tag);
    let ret = execute(instruction);
    match exc {
      None() => {
        assert(ret == RETIRE_SUCCESS);
        if outIsCap then
          assert(Y(outR) == outCap)
        else
          assert(X(outR) == outBits);
      },
      Some(code) => {
        assert(ret == RETIRE_FAIL);
        assert(mcause[Cause] == zero_extend(ext_exc_type_to_bits(EXC_CHERI(code))));
      }
    };
}

function test_cheri_malformed() -> unit = {
    // Create capabilities that are malformed in various ways
    let badBoundsCap = { root_cap with B = ones() };
    assert(boundsMalformed(badBoundsCap));
    let badPermsCap = { root_cap with ap_m = (if xlen == 32 then 0b10001 else 0b000010111) };
    assert(permsMalformed(badPermsCap));
    let badReservedCap = { root_cap with reserved_0 = ones() };
    assert(not(capReservedValid(badReservedCap)));

    let capR : regidx = Regidx(0b00001);
    let otherR : regidx = Regidx(0b00010);
    let outR : regidx = Regidx(0b00011);

    // Instructions like YMV that don't touch the fields should leave the bits untouched.
    let instr = YMV(outR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, badBoundsCap  , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, badPermsCap   , undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, badReservedCap, undefined);

    // Instructions that do a representability check should clear on any malformed fields
    // Do an YADDRW to zero (all input caps have address zero, so this will otherwise pass
    // the input through.
    let instr = YADDRW(outR, capR, otherR);
    X(otherR) = zeros();
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, {badBoundsCap with tag=false}   , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, {badPermsCap with tag=false}    , undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, {badReservedCap with tag=false} , undefined);

    // YPERMC legalises the *perms*. Clears tag if any fields malformed
    let instr = YPERMC(outR, capR, otherR);
    X(otherR) = zeros();
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, {badBoundsCap with ap_m = zeros(), tag=false}   , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, {badPermsCap with ap_m = zeros(), tag=false}    , undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, {badReservedCap with ap_m = zeros(), tag=false} , undefined);

    // YSS checks all the fields.
    let (_, zeroCapTagged) = setCapBounds({ null_cap with tag=true }, zeros(), zeros());

    Y(otherR) = zeroCapTagged;
    let instr = YSS(outR, capR, otherR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(root_cap      , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    let instr = YSS(outR, otherR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(root_cap      , capR, outR, instr, None(), false, undefined, zeros());

    Y(otherR) = root_cap;
    let instr = YSS(outR, capR, otherR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(root_cap      , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    let instr = YSS(outR, otherR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(root_cap      , capR, outR, instr, None(), false, undefined, zero_extend(0b1));

    // Dereference checks all the fields.
    let instr = LoadCapImm(outR, capR, zeros());
    assert_behaviour(badBoundsCap  , capR, outR, instr, Some(CapCheckType_Ld()), false, undefined, undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, Some(CapCheckType_Ld()), false, undefined, undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, Some(CapCheckType_Ld()), false, undefined, undefined);

    // CSR writes check all the fields
    write_ylen_csr(csr_name_map("ddc"), badBoundsCap);
    assert(not(ddc_y.tag));
    write_ylen_csr(csr_name_map("ddc"), badPermsCap);
    assert(not(ddc_y.tag));
    write_ylen_csr(csr_name_map("ddc"), badReservedCap);
    assert(not(ddc_y.tag));
    write_ylen_csr(csr_name_map("ddc"), root_cap);
    assert(ddc_y.tag);
}

function test_cheri_invalid_addr() -> unit = {
    // Very invalid address: top bits are not a sign-extension of lower bits
    let invalidAddr = 0b1 @ zeros(xlen - 1);
    // If system has no invalid addresses, escape
    if (validAddr(invalidAddr)) then return ();
    // Since invalid addr checks are waived for infinite caps, make a slightly smaller cap
    let (_, finite_cap) = setCapBounds(root_cap, zeros(), zero_extend(0xff00_0000_0000_0000));
    let infiniteR : regidx = Regidx(0b00001);
    let finiteR : regidx = Regidx(0b00010);
    let zeroR : regidx = Regidx(0b00000);
    // Attempt to jump to the invalid address with a capability jump
    Y(infiniteR) = {root_cap with address=invalidAddr};
    Y(finiteR) = {finite_cap with address=invalidAddr};
    assert(execute(JALR_capmode(zeros(), infiniteR, zeroR)) == RETIRE_SUCCESS);
    // Jump itself should retire
    assert(execute(JALR_capmode(zeros(), finiteR  , zeroR)) == RETIRE_SUCCESS);
    // Subsequent fetch must trap
    tick_pc();
    assert(fetch() == F_Ext_Error());
    // Attempt to jump to the invalid address with an integer jump
    PCC = Y(infiniteR);
    assert(execute(RISCV_JALR(zeros(), finiteR, zeroR)) == RETIRE_SUCCESS);
    PCC = Y(finiteR);
    // Subsequent fetch must trap
    tick_pc();
    assert(fetch() == F_Ext_Error());
    // Attempt to load from the invalid address
    ddc_y = Y(infiniteR);
    assert(execute(LOAD(zeros(), finiteR, zeroR, true, BYTE, false, false)) == RETIRE_SUCCESS);
    ddc_y = Y(finiteR);
    assert(execute(LOAD(zeros(), finiteR, zeroR, true, BYTE, false, false)) == RETIRE_FAIL);
    assert(mcause[Cause] == zero_extend(ext_exc_type_to_bits(EXC_CHERI(CapCheckType_Ld()))));
}

function test_cheri_feature_enables(priv : Privilege, cheri_allowed : bool, expected_mode : ExecutionMode) -> unit = {
    set_cur_privilege(priv);
    let backupPCC = PCC;
    assert(effective_cheri_mode() == expected_mode);
    let ddcAddr = csr_name_map("ddc");
    let resR : regidx = Regidx(0b00001);
    // Capmode has expected tag-preserving behaviour
    let auipcEnc = encdec(UTYPE(0x00000, resR, RISCV_AUIPC));
    assert(execute(ext_decode(auipcEnc)) == RETIRE_SUCCESS);
    assert(Y(resR).tag == (expected_mode == CapPtrMode));
    // Can access YLEN-width CSRs iff not prevented by some cre
    assert(execute(CSR(ddcAddr, resR, resR, false, CSRRW)) == (if cheri_allowed then RETIRE_SUCCESS else RETIRE_FAIL));
    // Restore things, as above might have trapped!
    PCC = backupPCC;
    set_cur_privilege(priv);
    // CHERI-only mode-independent instructions are allowed iff not prevented by some cre
    let resR = regidx_bits(resR);
    let instEnc = 0b0001000 @ 0b00001 @ resR @ 0b000 @ resR @ 0b0110011; // ypermr manually encoded as encdec depends on mode!
    assert(execute(ext_decode(instEnc)) == (if cheri_allowed then RETIRE_SUCCESS else RETIRE_FAIL));
}

function test_cheri_pcc_mode(priv : Privilege, cheri_allowed : bool) -> unit = {
    PCC = setCapMode(PCC, IntPtrMode);
    test_cheri_feature_enables(priv, cheri_allowed, IntPtrMode);
    PCC = setCapMode(PCC, CapPtrMode);
    test_cheri_feature_enables(priv, cheri_allowed, if cheri_allowed then CapPtrMode else IntPtrMode);
}

function test_cheri_reserved_branches() -> unit = {
    let instBitsBEQBad = encdec(BTYPE(zeros(), Regidx(0b00010), Regidx(0b00001), RISCV_BEQ));
    let instBitsBEQGood = encdec(BTYPE(zeros(), Regidx(0b00001), Regidx(0b00010), RISCV_BEQ));
    let instBitsBNEBad = encdec(BTYPE(zeros(), Regidx(0b00010), Regidx(0b00001), RISCV_BNE));
    let instBitsBNEGood = encdec(BTYPE(zeros(), Regidx(0b00001), Regidx(0b00010), RISCV_BNE));
    // Check that integer mode works with all branches
    PCC = {setCapMode(PCC, IntPtrMode)};
    let ast = ext_decode(instBitsBEQGood);
    assert(execute(ast) == RETIRE_SUCCESS);
    let ast = ext_decode(instBitsBEQBad);
    assert(execute(ast) == RETIRE_SUCCESS);
    let ast = ext_decode(instBitsBNEGood);
    assert(execute(ast) == RETIRE_SUCCESS);
    let ast = ext_decode(instBitsBNEBad);
    assert(execute(ast) == RETIRE_SUCCESS);
    // Check that cap mode allows the "good" instructions
    PCC = {setCapMode(PCC, CapPtrMode)};
    let ast = ext_decode(instBitsBEQGood);
    assert(execute(ast) == RETIRE_SUCCESS);
    let ast = ext_decode(instBitsBNEGood);
    assert(execute(ast) == RETIRE_SUCCESS);
    // Check that cap mode bans the "bad" instructions
    let ast = ext_decode(instBitsBEQBad);
    assert(execute(ast) == RETIRE_FAIL);
    assert_illegal_cause();
    let ast = ext_decode(instBitsBNEBad);
    assert(execute(ast) == RETIRE_FAIL);
    assert_illegal_cause();
}

function test_cheri_scre(cheri_allowed : bool) -> unit = {
    set_senvcfg(update_Y(senvcfg, 0b1).bits);
    test_cheri_pcc_mode(User, cheri_allowed);
    set_senvcfg(update_Y(senvcfg, 0b0).bits);
    test_cheri_pcc_mode(User, false);
}

function test_cheri_mcre(cheri_allowed : bool) -> unit = {
    set_menvcfg(update_Y(menvcfg, 0b1).bits);
    test_cheri_pcc_mode(Supervisor, cheri_allowed);
    test_cheri_scre(cheri_allowed);
    set_menvcfg(update_Y(menvcfg, 0b0).bits);
    test_cheri_pcc_mode(Supervisor, false);
    test_cheri_scre(false);
}

function test_cheri_enables() -> unit = {
    misa[Y] = 0b1;
    test_cheri_pcc_mode(Machine, true);
    test_cheri_mcre(true);
    misa[Y] = 0b0;
    test_cheri_pcc_mode(Machine, false);
    test_cheri_mcre(false);
}

function test_cheri_oob_jump() -> unit = {
    // Make a small cap
    let (_, finite_cap) = setCapBounds(root_cap, zeros(), zero_extend(0x100));
    let infiniteR : regidx = Regidx(0b00001);
    let finiteR : regidx = Regidx(0b00010);
    let zeroR : regidx = Regidx(0b00000);
    let bigR : regidx = Regidx(0b00011);
    // Attempt to jump in-bounds
    Y(infiniteR) = root_cap;
    Y(finiteR) = finite_cap;

    // In-bounds cap jump
    assert(execute(JALR_capmode(zeros(), infiniteR, zeroR)) == RETIRE_SUCCESS);
    assert(execute(ITYPE (zeros(), zeroR, zeroR, RISCV_ADDI)) == RETIRE_SUCCESS);

    // Out-of-bounds cap jump
    // Jump itself should retire
    assert(execute(JALR_capmode(0x200, finiteR, zeroR)) == RETIRE_SUCCESS);
    // Subsequent fetch must trap
    tick_pc();
    assert(PCC.tag);
    assert(fetch() == F_Ext_Error());

    // Attempt to jump out of PCC
    PCC = finite_cap;
    // Jump itself should retire
    assert(execute(RISCV_JALR(0x200, zeroR, zeroR)) == RETIRE_SUCCESS);
    // Subsequent fetch must trap
    tick_pc();
    assert(PCC.tag);
    assert(fetch() == F_Ext_Error());

    // Jump so far it must make PCC unrepresentable
    PCC = finite_cap;
    X(bigR) = zero_extend(0x80000000);
    // Jump itself should retire
    assert(execute(RISCV_JALR(zeros(), bigR, zeroR)) == RETIRE_SUCCESS);
    // Subsequent fetch must trap
    tick_pc();
    assert(not(PCC.tag));
    assert(fetch() == F_Ext_Error());

    PCC = root_cap;
}

function test_main_ext() -> unit = {
    // Enable CHERI
    misa[Y] = 0b1;
    set_menvcfg(update_Y(menvcfg, 0b1).bits);
    set_senvcfg(update_Y(senvcfg, 0b1).bits);

    //test_cheri_sdtrig();
    debug_mode_active = false;

    test_cheri_cap_encoding();
    test_cheri_yamask();
    test_cheri_fault();
    test_cheri_system_faults();
    test_cheri_nofastrep();
    test_cheri_zba();
    test_cheri_l8();
    test_cheri_redundant();
    test_cheri_reserved_branches();
    test_cheri_rounding();
    test_cheri_permission_encoding();
    test_cheri_circular();
    test_cheri_ylen_csr();
    test_cheri_csr_access_control();
    test_cheri_malformed();
    test_cheri_invalid_addr();
    test_cheri_oob_jump();
    //test_cheri_enables(); Disable while cheri enables hardwired high
    print("CHERI tests passed\n");
}
