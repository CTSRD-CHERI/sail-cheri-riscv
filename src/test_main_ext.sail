function test_cheri_cap_encoding() -> unit = {
    // Check the null cap decodes from all 0s.
    // In future we will encode it from all 0s so we won't need to check that.
    assert(bitsToCap(false, zeros()) == null_cap, "zeros don't decode to null capability");
    assert(capToMetadataBits(null_cap).bits == zeros(), "null capability doesn't encode to zeros");
}

function test_cheri_cram() -> unit = {
    // Check the mask for 0 length is all ones.
    assert(getRepresentableAlignmentMask(zeros()) == ones());
}

function test_cheri_xtval() -> unit = {
    let zeroR = 0b00000;
    // Check that CHERI exceptions are reported in MTVAL
    PCC = {setCapMode(PCC, CapPtrMode)};
    assert(execute(LoadCapImm(zeroR, zeroR, zeros())) == RETIRE_FAIL); // Throw tag exception
    assert(mtval == zeros(sizeof(xlen - 20)) @
           capchecktype_code(CapCheckType_Data) @
           zeros(12) @
           capex_code(CapEx_TagViolation));
}

function test_cheri_sdtrig() -> unit = {
  set_cur_privilege(Machine);
  assert (not(debug_mode_active));
  let addr : xlenbits = zero_extend(0x01234567);
  let src = 0b00100;
  let rd = 0b00011;
  C(src) = { null_cap with address = addr };
  PCC = setCapMode(PCC, CapPtrMode);
  let ret = execute(LoadCapImm(rd, src, zeros()));
  assert (ret == RETIRE_FAIL);
  assert (mcause[Cause] == zero_extend (0x1C));
  assert (not(debug_mode_active));
  let tdata1 : xlenbits = 0x68 @ zeros(xlen - 24) @ 0x107f;
  write_tdata1_underlying(0, tdata1);
  write_tdata2_underlying(0, addr);
  PCC = setCapMode(PCC, CapPtrMode);
  let ret = execute(LoadCapImm(rd, src, zeros()));
  assert (ret == RETIRE_DEBUG_TRIGGER);
  assert (debug_mode_active);
  let _ = execute (DRET());
  assert (not(debug_mode_active));
  X(src) = addr;
  set_ddc(null_cap);
  PCC = setCapMode(PCC, IntPtrMode);
  let _ = execute(LOAD(zeros(), src, rd, true, BYTE, false, false));
  assert (ret == RETIRE_DEBUG_TRIGGER);
  assert (debug_mode_active);
}

function test_cheri_nofastrep () -> unit = {
    // Check that the representability check is exact, i.e. that the historical
    // "fast representability check" is not in use.
    let capR = 0b00001;
    let addrR = 0b00010;
    let outR = 0b00011;
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
    let (exact, cap) = setCapBounds({infinite_cap with address = base}, base, top);
    assert(exact);
    C(capR) = cap;
    X(addrR) = addr;
    assert(execute(SCADDR(capR, capR, addrR)) == RETIRE_SUCCESS);
    assert(C(capR).tag);
    // Perform the CADDI that would detag the capability if the fast
    // representability check is being used.
    assert(execute(CADDI(outR, capR, increment)) == RETIRE_SUCCESS);
    assert(C(outR).tag);
    // Check that incrementing by one more does in fact detag the
    // cap, i.e. that if the fast representability check's assumption
    // of a carry were accurate, then the capability should be
    // detagged.
    assert(execute(CADDI(outR, capR, increment+1)) == RETIRE_SUCCESS);
    assert(not(C(outR).tag));
}

val test_cheri_zba_mode : (bitvector(32), regidx) -> unit
function test_cheri_zba_mode(instBits, resR) = {
    // Check that integer mode uses integer instructions
    PCC = {setCapMode(PCC, IntPtrMode)};
    let ast = ext_decode(instBits);
    assert(execute(ast) == RETIRE_SUCCESS);
    assert(not(C(resR).tag));
    // Check that cap mode uses capability instructions
    PCC = {setCapMode(PCC, CapPtrMode)};
    let ast = ext_decode(instBits);
    assert(execute(ast) == RETIRE_SUCCESS);
    assert(C(resR).tag)
}

function test_cheri_zba() -> unit = {
    let capR = 0b00001;
    let indR = 0b00010;
    let resR = 0b00011;
    C(capR) = infinite_cap;
    X(indR) = to_bits(xlen, 1);
    C(resR) = infinite_cap;
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH1ADD)), resR);
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH2ADD)), resR);
    test_cheri_zba_mode(encdec(ZBA_RTYPE(capR, indR, resR, RISCV_SH3ADD)), resR);
    if xlen == 32 then () else {
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_ADDUW)), resR);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH1ADDUW)), resR);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH2ADDUW)), resR);
        test_cheri_zba_mode(encdec(ZBA_RTYPEUW(capR, indR, resR, RISCV_SH3ADDUW)), resR);
        test_cheri_zba_mode(encdec(ZBA_SH4ADD(capR, indR, resR)), resR);
        test_cheri_zba_mode(encdec(ZBA_SH4ADDUW(capR, indR, resR)), resR);
    }
}

// Verify that setting the bounds on C(capR) based on C(capR) and X(lenR)
// gives the expected result.
function check_format(
    capR : bits(5),
    lenR : bits(5),
    dstR : bits(5),
    aimE : CapExponent,
    aimIE : bool,
    aimLen : CapLenBits,
) -> unit = {
    assert(execute(SCBNDS(dstR, capR, lenR)) == RETIRE_SUCCESS);
    assert(C(dstR).internal_exponent == aimIE);
    assert(C(dstR).E == aimE);
    assert(to_bits(cap_len_width, getCapLength(C(dstR))) == aimLen);
}

function test_cheri_l8() -> unit = {
    if (xlen != 32) then return ();
    let capR = 0b00001;
    let lenR = 0b00010;
    let dstR = 0b00011;
    C(capR) = infinite_cap;
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
         infinite_cap with
         E = 0,
         B = zeros(),
         T = 0b01 @ zeros(cap_mantissa_width - 2),
         internal_exponent = true,
      };
    let goodCap =
      {
         infinite_cap with
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
    let capR = 0b00001;
    let lenR = 0b00010;
    let outR = 0b00011;
    C(capR) = {infinite_cap with address = to_bits(xlen, 1)};
    X(lenR) = 0b1 @ ones(sizeof(xlen - 2)) @ 0b1; // very unaligned
    // Check that SCBNDS is exact
    let _ = execute(SCBNDS(outR, capR, lenR));
    assert(not(C(outR).tag));
    // Check that SCBNDSR rounds
    let _ = execute(SCBNDSR(outR, capR, lenR));
    assert(C(outR).tag);
    // Check that SCBNDSI doesn't assert with max requested len
    let _ = execute(SCBNDSI(outR, capR, 0b0, ones()));
    assert(C(outR).tag);
    let _ = execute(SCBNDSI(outR, capR, 0b1, ones()));
    assert(C(outR).tag);
}

function test_cheri_permission_encoding() -> unit = {
    // Verify that SCMODE doesn't affect other permissions bits even if they have
    // malformed permissions.
    let capR =  0b00001;
    let modeR = 0b00010;
    let dstR =  0b00011;
    if cap_size == 16 then {
        // Malformed permission combination, but it can be encoded (though is reserved) on RV64.
        // M=1 (IntPtrMode), LM=0 ASR=1, X=0, R=1, W=1, C=0
        let invalid = {null_cap with ap_m = 0b1010110};
        // We shouldn't be able to change the mode to CapPtrMode because X=0
        // so this should have no effect.
        C(capR) = invalid;
        X(modeR) = zero_extend(execution_mode_encdec(CapPtrMode));
        assert(execute(SCMODE(dstR, capR, modeR)) == RETIRE_SUCCESS);
        assert(C(dstR) == invalid)
    };

    // Test that clearing the X permission of a capability with M=1 (IntPtrMode)
    // clears M (CapPtrMode).
    let intmode_inf = setCapMode(infinite_cap, IntPtrMode);
    assert(getCapMode(intmode_inf) == IntPtrMode);
    let all_perms_but_x = {getArchPermsLegalized(intmode_inf) with X=false};
    let cap_x_cleared = setArchPerms(intmode_inf, all_perms_but_x);
    assert(getCapMode(cap_x_cleared) == CapPtrMode);
}

function test_cheri_circular() -> unit = {
    let capR = 0b00001;
    let valR = 0b00010;
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
    };
    // Since PMAs can't encode a 2^XLEN region we'll just have two regions.
    let half_mem = 0b1 @ zeros(xlen - 1);
    let region_0 : PMA_Region = struct {
      base       = zeros(),
      size       = half_mem,
      attributes = attr,
    };
    let region_1 : PMA_Region = struct {
      base       = half_mem,
      size       = half_mem,
      attributes = attr,
    };
    pma_regions = [| region_0, region_1 |];

    // Write to low end of address space
    X(valR) = zeros(sizeof(xlen - 8)) @ 0xbe;
    C(capR) = { infinite_cap with address = to_bits(xlen, 0) };
    assert(execute(STORE(zeros(), valR, capR, BYTE, false, false)) == RETIRE_SUCCESS);
    // Write to high end of address space
    X(valR) = zeros(sizeof(xlen - 8)) @ 0xef;
    C(capR) = { infinite_cap with address = to_bits(xlen, -1) };
    assert(execute(STORE(zeros(), valR, capR, BYTE, false, false)) == RETIRE_SUCCESS);
    // Perform wrapping read
    assert(execute(LOAD(zeros(), capR, valR, true, HALF, false, false)) == RETIRE_SUCCESS);
    // Check we got the right answer
    assert(X(valR) == zeros(sizeof(xlen - 16)) @ 0xbeef)
}

function test_cheri_clen_csr() -> unit = {
    let csr : csreg = csr_name_map("mtvec");
    let (_, capTest) = setCapBounds(infinite_cap, zero_extend(0x00010000), zero_extend(0x00020000));
    let src = 0b00100;
    let dst = 0b00101;
    let tmp = 0b11000;
    C(src) = capTest;
    /////////////////////////////////////////////
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, true, false);
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(C(src) == C(dst));
    assert(C(dst) == capTest);
    /////////////////////////////////////////////
    let addr : xlenbits = zero_extend(0x00010111);
    X(tmp) = addr;
    PCC = {setCapMode(PCC, IntPtrMode)};
    let _ = handle_csr_op(csr, tmp, dst, false, CSRRW, true, false);
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(C(dst) == {capTest with address = addr});
    let addr2 : xlenbits = zero_extend(0x00070111);
    X(tmp) = addr2;
    PCC = {setCapMode(PCC, IntPtrMode)};
    let _ = handle_csr_op(csr, tmp, dst, false, CSRRW, true, false);
    PCC = {setCapMode(PCC, CapPtrMode)};
    let _ = handle_csr_op(csr, src, dst, false, CSRRW, false, true);
    assert(C(dst) == {capTest with address = addr2, tag = false});
}

function attempt_csr_access(priv : Privilege, asr : bool, op : csrop, csr : csreg, src : regidx, dst : regidx) -> Retired = {
    set_cur_privilege(priv);
    PCC = setArchPerms(PCC, {getArchPermsLegalized(PCC) with ASR=asr});
    execute(CSR(csr, src, dst, false, op))
}

function test_csr_access_priv_asr_rw(csr : string, priv : Privilege, asr : bool, write : bool, allowed : bool) -> unit = {
    C(0b00001) = infinite_cap;
    let src = if write then 0b00001 else zreg;
    let dst = if write then zreg else 0b00001;
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
    test_csr_access("mtdc"     , Machine   , false, true , true);
    test_csr_access("stdc"     , Supervisor, false, true , true);
    test_csr_access("mtidc"    , Machine   , false, true , false);
    test_csr_access("stidc"    , Supervisor, false, true , false);
    test_csr_access("utidc"    , User      , false, true , false);
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
                          exc : option(CapEx),
                          outIsCap : bool,
                          outCap : Capability,
                          outBits : xlenbits) -> unit = {
    C(capR) = inCap;
    assert(C(capR).tag);
    let ret = execute(instruction);
    match exc {
      None() => {
        assert(ret == RETIRE_SUCCESS);
        if outIsCap then
          assert(C(outR) == outCap)
        else
          assert(X(outR) == outBits);
      },
      Some(code) => {
        assert(ret == RETIRE_FAIL);
        assert(mcause[Cause] == zero_extend (0x1C));
	assert(mtval[3..0] == capex_code(code));
      }
    };
}

function test_cheri_malformed() -> unit = {
    // Create capabilities that are malformed in various ways
    let badBoundsCap = { infinite_cap with B = ones() };
    assert(boundsMalformed(badBoundsCap));
    let badPermsCap = { infinite_cap with ap_m = (if xlen == 32 then 0b10001 else 0b0010111) };
    assert(permsMalformed(badPermsCap));
    let badReservedCap = { infinite_cap with reserved_0 = ones() };
    assert(not(capReservedValid(badReservedCap)));

    let capR = 0b00001;
    let otherR = 0b00010;
    let outR = 0b00011;

    // Instructions like CMV that don't touch the fields should leave the bits untouched.
    let instr = CMV(outR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, badBoundsCap  , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, badPermsCap   , undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, badReservedCap, undefined);

    // Instructions that do a representability check should clear on malformed *bounds*.
    // Do an SCADDR to zero (all input caps have address zero, so this will otherwise pass
    // the input through.
    let instr = SCADDR(outR, capR, otherR);
    X(otherR) = zeros();
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, {badBoundsCap with tag=false}   , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, badPermsCap                     , undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, {badReservedCap with tag=false} , undefined);

    // ACPERM legalises the *perms*
    let instr = ACPERM(outR, capR, otherR);
    X(otherR) = ones();
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), true, badBoundsCap                     , undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), true, {badPermsCap with ap_m = zeros()}, undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, None(), true, {badReservedCap with tag=false}  , undefined);

    // SCSS checks all the fields.
    let (_, zeroCapTagged) = setCapBounds({ null_cap with tag=true }, zeros(), zeros());

    C(otherR) = zeroCapTagged;
    let instr = SCSS(outR, capR, otherR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(infinite_cap  , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    let instr = SCSS(outR, otherR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(infinite_cap  , capR, outR, instr, None(), false, undefined, zeros());

    C(otherR) = infinite_cap;
    let instr = SCSS(outR, capR, otherR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(infinite_cap  , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    let instr = SCSS(outR, otherR, capR);
    assert_behaviour(badBoundsCap  , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badPermsCap   , capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(badReservedCap, capR, outR, instr, None(), false, undefined, zeros());
    assert_behaviour(zeroCapTagged , capR, outR, instr, None(), false, undefined, zero_extend(0b1));
    assert_behaviour(infinite_cap  , capR, outR, instr, None(), false, undefined, zero_extend(0b1));

    // Dereference checks all the fields.
    let instr = LoadCapImm(outR, capR, zeros());
    assert_behaviour(badBoundsCap  , capR, outR, instr, Some(CapEx_LengthViolation)    , false, undefined, undefined);
    assert_behaviour(badPermsCap   , capR, outR, instr, Some(CapEx_PermissionViolation), false, undefined, undefined);
    assert_behaviour(badReservedCap, capR, outR, instr, Some(CapEx_TagViolation)       , false, undefined, undefined);

    // CSR writes check all the fields
    write_clen_csr(csr_name_map("ddc"), badBoundsCap);
    assert(not(ddc.tag));
    write_clen_csr(csr_name_map("ddc"), badPermsCap);
    assert(not(ddc.tag));
    write_clen_csr(csr_name_map("ddc"), badReservedCap);
    assert(not(ddc.tag));
    write_clen_csr(csr_name_map("ddc"), infinite_cap);
    assert(ddc.tag);
}

function test_cheri_invalid_addr() -> unit = {
    // No invalid addresses on RV32
    if xlen == 32 then return ();
    // Very invalid address: top bits are not a sign-extension of lower bits
    let invalidAddr = 0b1 @ zeros(xlen - 1);
    // Since invalid addr checks are waived for infinite caps, make a slightly smaller cap
    let (_, finite_cap) = setCapBounds(infinite_cap, zeros(), zero_extend(0xff00_0000_0000_0000));
    let infiniteR = 0b00001;
    let finiteR = 0b00010;
    let zeroR = 0b00000;
    // Attempt to jump to the invalid address with a capability jump
    C(infiniteR) = {infinite_cap with address=invalidAddr};
    C(finiteR) = {finite_cap with address=invalidAddr};
    assert(execute(JALR_capmode(zeros(), infiniteR, zeroR)) == RETIRE_SUCCESS);
    assert(execute(JALR_capmode(zeros(), finiteR  , zeroR)) == RETIRE_FAIL);
    assert(mtval == zeros(sizeof(xlen - 20)) @
           capchecktype_code(CapCheckType_JBr) @
           zeros(12) @
           capex_code(CapEx_InvalidAddressViolation));
    // Attempt to jump to the invalid address with an integer jump
    PCC = C(infiniteR);
    assert(execute(RISCV_JALR(zeros(), finiteR, zeroR)) == RETIRE_SUCCESS);
    PCC = C(finiteR);
    assert(execute(RISCV_JALR(zeros(), finiteR, zeroR)) == RETIRE_FAIL);
    assert(mtval == zeros(sizeof(xlen - 20)) @
           capchecktype_code(CapCheckType_JBr) @
           zeros(12) @
           capex_code(CapEx_InvalidAddressViolation));
    // Attempt to load from the invalid address
    ddc = C(infiniteR);
    assert(execute(LOAD(zeros(), finiteR, zeroR, true, BYTE, false, false)) == RETIRE_SUCCESS);
    ddc = C(finiteR);
    assert(execute(LOAD(zeros(), finiteR, zeroR, true, BYTE, false, false)) == RETIRE_FAIL);
    assert(mtval == zeros(sizeof(xlen - 20)) @
           capchecktype_code(CapCheckType_Data) @
           zeros(12) @
           capex_code(CapEx_InvalidAddressViolation));
}

function test_cheri_feature_enables(priv : Privilege, cheri_allowed : bool, expected_mode : ExecutionMode) -> unit = {
    set_cur_privilege(priv);
    let backupPCC = PCC;
    assert(effective_cheri_mode() == expected_mode);
    let ddcAddr = csr_name_map("ddc");
    let resR = 0b00001;
    // Capmode has expected tag-preserving behaviour
    let auipcEnc = encdec(UTYPE(0x00000, resR, RISCV_AUIPC));
    assert(execute(ext_decode(auipcEnc)) == RETIRE_SUCCESS);
    assert(C(resR).tag == (expected_mode == CapPtrMode));
    // Can access CLEN-width CSRs iff not prevented by some cre
    assert(execute(CSR(ddcAddr, resR, resR, false, CSRRW)) == (if cheri_allowed then RETIRE_SUCCESS else RETIRE_FAIL));
    // Restore things, as above might have trapped!
    PCC = backupPCC;
    set_cur_privilege(priv);
    // CHERI-only mode-independent instructions are allowed iff not prevented by some cre
    let instEnc = 0b0001000 @ 0b00001 @ resR @ 0b000 @ resR @ 0b0110011; // gcperm manually encoded as encdec depends on mode!
    assert(execute(ext_decode(instEnc)) == (if cheri_allowed then RETIRE_SUCCESS else RETIRE_FAIL));
}

function test_cheri_pcc_mode(priv : Privilege, cheri_allowed : bool) -> unit = {
    PCC = setCapMode(PCC, IntPtrMode);
    test_cheri_feature_enables(priv, cheri_allowed, IntPtrMode);
    PCC = setCapMode(PCC, CapPtrMode);
    test_cheri_feature_enables(priv, cheri_allowed, if cheri_allowed then CapPtrMode else IntPtrMode);
}

function test_cheri_scre(cheri_allowed : bool) -> unit = {
    set_senvcfg(update_CRE(senvcfg, 0b1).bits());
    test_cheri_pcc_mode(User, cheri_allowed);
    set_senvcfg(update_CRE(senvcfg, 0b0).bits());
    test_cheri_pcc_mode(User, false);
}

function test_cheri_mcre(cheri_allowed : bool) -> unit = {
    set_menvcfg(update_CRE(menvcfg, 0b1).bits());
    test_cheri_pcc_mode(Supervisor, cheri_allowed);
    test_cheri_scre(cheri_allowed);
    set_menvcfg(update_CRE(menvcfg, 0b0).bits());
    test_cheri_pcc_mode(Supervisor, false);
    test_cheri_scre(false);
}

function test_cheri_enables() -> unit = {
    set_mseccfg(update_CRE(mseccfg, 0b1).bits());
    test_cheri_pcc_mode(Machine, true);
    test_cheri_mcre(true);
    set_mseccfg(update_CRE(mseccfg, 0b0).bits());
    test_cheri_pcc_mode(Machine, false);
    test_cheri_mcre(false);
}

function test_main_ext() -> unit = {
    // Enable CHERI
    set_mseccfg(update_CRE(mseccfg, 0b1).bits());
    set_menvcfg(update_CRE(menvcfg, 0b1).bits());
    set_senvcfg(update_CRE(senvcfg, 0b1).bits());

    test_cheri_sdtrig();
    debug_mode_active = false;

    test_cheri_cap_encoding();
    test_cheri_cram();
    test_cheri_xtval();
    test_cheri_nofastrep();
    test_cheri_zba();
    test_cheri_l8();
    test_cheri_redundant();
    test_cheri_rounding();
    test_cheri_permission_encoding();
    test_cheri_circular();
    test_cheri_clen_csr();
    test_cheri_csr_access_control();
    test_cheri_malformed();
    test_cheri_invalid_addr();
    test_cheri_enables();
}
