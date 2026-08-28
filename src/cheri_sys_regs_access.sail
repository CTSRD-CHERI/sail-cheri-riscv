// This file contains overrides for accessing YLEN extended CSRs and their
// XLEN aliases.
//
// E.g. for `mtvec[c]` we have:
//
// * get_mtvec(): XLEN read
// * set_mtvec(): XLEN write
// * set_mtvec_y(): YLEN write
//
// There's no need for YLEN read functions since they're only used in CHERI and
// would always be just returning the register value directly.

/******************************* xTVEC *******************************/

function tvec_y_vector_range_check(tvec: Capability) -> Capability = {
  // Check representability of base address with mode bits zeroed
  let (representable, _) = setCapAddr(tvec, tvec_base_addr(Mk_Mtvec(tvec.address)));
  let tvec = clearTagIf(tvec, not(representable));
  if Mk_Mtvec(tvec.address)[Mode] != trapVectorMode_bits(TV_Vector) then return tvec;

  // If in vectored mode, also check maximum vector address
  let max_interrupt = if extensionEnabled(Ext_Sscofpmf) then Local_Counter_Overflow else I_M_External;
  let max_mcause = [ Mk_Mcause(zeros()) with
    Cause = zero_extend(interruptType_to_bits(max_interrupt)),
    IsInterrupt = 0b1,
  ];
  let max_cause_addr : xlenbits = match tvec_addr(Mk_Mtvec(tvec.address), max_mcause) {
    Some(addr) => addr,
    None() => internal_error(__FILE__, __LINE__, "tvec_addr should return an address"),
  };
  let (representable, c) = setCapAddr(tvec, max_cause_addr);
  clearTagIf(tvec, not(representable) | not(convertInvalidAddr(c).tag))
}

function legalize_tvec_y(o : Capability, v : Capability) -> Capability = {
  let new_tvec = v.address;
  let legalized_tvec = legalize_tvec(Mk_Mtvec(o.address), new_tvec);
  tvec_y_vector_range_check(setCapAddrChecked(v, legalized_tvec.bits))
}

function get_mtvec() -> xlenbits = mtvec_y.address
function get_stvec() -> xlenbits = stvec_y.address

function set_mtvec(value : xlenbits) -> unit = {
  let mtv = legalize_tvec(Mk_Mtvec(mtvec_y.address), convertInvalidAddr(value));
  mtvec_y = tvec_y_vector_range_check(setCapCSRAddr(mtvec_y, mtv.bits));
}

function set_stvec(value : xlenbits) -> unit = {
  let stv = legalize_tvec(Mk_Mtvec(stvec_y.address), convertInvalidAddr(value));
  stvec_y = tvec_y_vector_range_check(setCapCSRAddr(stvec_y, stv.bits));
}

function set_mtvec_y(value : Capability) -> unit = {
  mtvec_y = legalize_tvec_y(mtvec_y, convertInvalidAddr(value));
}

function set_stvec_y(value : Capability) -> unit = {
  stvec_y = legalize_tvec_y(stvec_y, convertInvalidAddr(value));
}

/******************************* xSCRATCH *******************************/

function get_mscratch() -> xlenbits = mscratch_y.address
function get_sscratch() -> xlenbits = sscratch_y.address

function set_mscratch(value : xlenbits) -> unit = {
  mscratch_y = setCapAddrChecked(mscratch_y, value);
}

function set_sscratch(value : xlenbits) -> unit = {
  sscratch_y = setCapAddrChecked(sscratch_y, value);
}

function set_mscratch_y(value : Capability) -> unit = {
  mscratch_y = value;
}

function set_sscratch_y(value : Capability) -> unit = {
  sscratch_y = value;
}

/******************************* xEPC[C] *******************************/

function get_mepc() -> xlenbits = align_pc(mepc_y.address)
function get_sepc() -> xlenbits = align_pc(sepc_y.address)

function set_mepc(value : xlenbits) -> unit = {
  mepc_y = setCapCSRAddr(mepc_y, legalize_xepc(convertInvalidAddr(value)));
}

function set_sepc(value : xlenbits) -> unit = {
  sepc_y = setCapCSRAddr(sepc_y, legalize_xepc(convertInvalidAddr(value)));
}

function set_mepc_y(value : Capability) -> unit = {
  mepc_y = legalize_epc_y(convertInvalidAddr(value));
}

function set_sepc_y(value : Capability) -> unit = {
  sepc_y = legalize_epc_y(convertInvalidAddr(value));
}

/******************************* DDC *******************************/

function set_ddc_y(value : Capability) -> unit = {
  ddc_y = convertInvalidAddrCap(value);
}

function set_ddc_xlen(value : xlenbits) -> unit = {
  ddc_y = setCapCSRAddr(ddc_y, convertInvalidAddr(value));
}

/******************************* xTID *******************************/

function is_zstid_csr (csrno : bits(12)) -> bool =
  csr_name_map(csrno) == "mtid" | csr_name_map(csrno) == "stid" | csr_name_map(csrno) == "utid"

function get_mtid() -> xlenbits = mtid_y.address
function get_stid() -> xlenbits = stid_y.address
function get_utid() -> xlenbits = utid_y.address

function set_mtid_y(value : Capability) -> unit = {
  mtid_y = value;
}

function set_stid_y(value : Capability) -> unit = {
  stid_y = value;
}

function set_utid_y(value : Capability) -> unit = {
  utid_y = value;
}

function set_mtid(value : xlenbits) -> unit = {
  mtid_y = setCapAddrChecked(mtid_y, value);
}

function set_stid(value : xlenbits) -> unit = {
  stid_y = setCapAddrChecked(stid_y, value);
}

function set_utid(value : xlenbits) -> unit = {
  utid_y = setCapAddrChecked(utid_y, value);
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
