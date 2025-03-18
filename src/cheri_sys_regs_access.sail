// This file contains overrides for accessing CLEN extended CSRs and their
// XLEN aliases.
//
// E.g. for `mtvec[c]` we have:
//
// * get_mtvec(): XLEN read
// * set_mtvec(): XLEN write
// * set_mtvecc(): CLEN write
//
// For the CLEN CSRs with no XLEN name, e.g. `ddc` we have:
//
// * get_ddc_xlen(): XLEN read
// * set_ddc(): CLEN write
// * set_ddc_xlen(): XLEN write.
//
// There's no need for CLEN read functions since they're only used in CHERI and
// would always be just returning the register value directly.

/******************************* xTVEC[C] *******************************/

function tvecc_vector_range_check(tvecc: Capability) -> Capability = {
  // Check representability of base address with mode bits zeroed
  let (representable, _) = setCapAddr(tvecc, tvec_base_addr(Mk_Mtvec(tvecc.address)));
  let tvecc = clearTagIf(tvecc, not(representable));
  if Mk_Mtvec(tvecc.address)[Mode] != trapVectorMode_bits(TV_Vector) then return tvecc;

  // If in vectored mode, also check maximum vector address
  let max_interrupt = if extensionEnabled(Ext_Sscofpmf) then Local_Counter_Overflow else I_M_External;
  let max_mcause = [ Mk_Mcause(zeros()) with
    Cause = zero_extend(interruptType_to_bits(max_interrupt)),
    IsInterrupt = 0b1,
  ];
  let max_cause_addr : xlenbits = match tvec_addr(Mk_Mtvec(tvecc.address), max_mcause) {
    Some(addr) => addr,
    None() => internal_error(__FILE__, __LINE__, "tvec_addr should return an address"),
  };
  let (representable, c) = setCapAddr(tvecc, max_cause_addr);
  clearTagIf(tvecc, not(representable) | not(convertInvalidAddr(c).tag))
}

function legalize_tvecc(o : Capability, v : Capability) -> Capability = {
  let new_tvec = v.address;
  let legalized_tvec = legalize_tvec(Mk_Mtvec(o.address), new_tvec);
  tvecc_vector_range_check(setCapAddrChecked(v, legalized_tvec.bits))
}

function get_mtvec() -> xlenbits = mtvecc.address
function get_stvec() -> xlenbits = stvecc.address

function set_mtvec(value : xlenbits) -> unit = {
  let mtv = legalize_tvec(Mk_Mtvec(mtvecc.address), convertInvalidAddr(value));
  mtvecc = tvecc_vector_range_check(setCapCSRAddr(mtvecc, mtv.bits));
}

function set_stvec(value : xlenbits) -> unit = {
  let stv = legalize_tvec(Mk_Mtvec(stvecc.address), convertInvalidAddr(value));
  stvecc = tvecc_vector_range_check(setCapCSRAddr(stvecc, stv.bits));
}

function set_mtvecc(value : Capability) -> unit = {
  mtvecc = legalize_tvecc(mtvecc, convertInvalidAddr(value));
}

function set_stvecc(value : Capability) -> unit = {
  stvecc = legalize_tvecc(stvecc, convertInvalidAddr(value));
}

/******************************* xSCRATCH[C] *******************************/

function get_mscratch() -> xlenbits = mscratchc.address
function get_sscratch() -> xlenbits = sscratchc.address

function set_mscratch(value : xlenbits) -> unit = {
  mscratchc = setCapAddrChecked(mscratchc, value);
}

function set_sscratch(value : xlenbits) -> unit = {
  sscratchc = setCapAddrChecked(sscratchc, value);
}

function set_mscratchc(value : Capability) -> unit = {
  mscratchc = value;
}

function set_sscratchc(value : Capability) -> unit = {
  sscratchc = value;
}

/******************************* xEPC[C] *******************************/

function get_mepc() -> xlenbits = align_pc(mepcc.address)
function get_sepc() -> xlenbits = align_pc(sepcc.address)

function set_mepc(value : xlenbits) -> unit = {
  mepcc = setCapCSRAddr(mepcc, legalize_xepc(convertInvalidAddr(value)));
}

function set_sepc(value : xlenbits) -> unit = {
  sepcc = setCapCSRAddr(sepcc, legalize_xepc(convertInvalidAddr(value)));
}

function set_mepcc(value : Capability) -> unit = {
  mepcc = legalize_epcc(convertInvalidAddr(value));
}

function set_sepcc(value : Capability) -> unit = {
  sepcc = legalize_epcc(convertInvalidAddr(value));
}

/******************************* DDC *******************************/

function get_ddc_xlen() -> xlenbits = ddc.address

function set_ddc(value : Capability) -> unit = {
  ddc = convertInvalidAddrCap(value);
}

function set_ddc_xlen(value : xlenbits) -> unit = {
  ddc = setCapCSRAddr(ddc, convertInvalidAddr(value));
}

/******************************* xTDC *******************************/

function get_mtdc_xlen() -> xlenbits = mtdc.address
function get_stdc_xlen() -> xlenbits = stdc.address

function set_mtdc(value : Capability) -> unit = {
  mtdc = value;
}

function set_stdc(value : Capability) -> unit = {
  stdc = value;
}

function set_mtdc_xlen(value : xlenbits) -> unit = {
  mtdc = setCapAddrChecked(mtdc, value);
}

function set_stdc_xlen(value : xlenbits) -> unit = {
  stdc = setCapAddrChecked(stdc, value);
}

/******************************* xTID[C] *******************************/

function is_zstid_csr (csrno : bits(12)) -> bool =
  csr_name_map(csrno) == "mtid" | csr_name_map(csrno) == "stid" | csr_name_map(csrno) == "utid"

function get_mtid() -> xlenbits = mtidc.address
function get_stid() -> xlenbits = stidc.address
function get_utid() -> xlenbits = utidc.address

function set_mtidc(value : Capability) -> unit = {
  mtidc = value;
}

function set_stidc(value : Capability) -> unit = {
  stidc = value;
}

function set_utidc(value : Capability) -> unit = {
  utidc = value;
}

function set_mtid(value : xlenbits) -> unit = {
  mtidc = setCapAddrChecked(mtidc, value);
}

function set_stid(value : xlenbits) -> unit = {
  stidc = setCapAddrChecked(stidc, value);
}

function set_utid(value : xlenbits) -> unit = {
  utidc = setCapAddrChecked(utidc, value);
}

/******************************* xenvcfg *******************************/

function set_menvcfg(v : bits(64)) -> unit = {
  menvcfg = legalize_menvcfg(menvcfg, mseccfg, v);
}

function set_senvcfg(v : xlenbits) -> unit = {
  senvcfg = legalize_senvcfg(senvcfg, menvcfg, v);
}

/******************************* mseccfg *******************************/

function set_mseccfg(v : bits(64)) -> unit = {
  mseccfg = legalize_mseccfg(mseccfg, v);
}

/******************************* xtval2 ********************************/

function legalize_tval2(o: Tval2, v: xlenbits) -> Tval2 = {
  let v = Mk_Tval2(v);
  [
    o with
    TYPE = v[TYPE],
    CAUSE = v[CAUSE],
  ]
}
