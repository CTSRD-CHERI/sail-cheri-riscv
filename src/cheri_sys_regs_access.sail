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
  // TODO (CLIC): This likely needs updating for CLIC (when specified)
  if Mk_Mtvec(tvecc.address)[Mode] != trapVectorMode_bits(TV_Vector) then return tvecc;
  let max_cause_addr = tvecc.address + zero_extend(interruptType_to_bits(I_M_External));
  let (representable, _) = setCapAddr(tvecc, max_cause_addr);
  clearTagIf(tvecc, not(representable))
}

function legalize_tvecc(o : Capability, v : Capability) -> Capability = {
  let new_tvec = v.address;
  let legalized_tvec = legalize_tvec(Mk_Mtvec(o.address), new_tvec);
  tvecc_vector_range_check(setCapAddrChecked(v, legalized_tvec.bits))
}

function get_mtvec() -> xlenbits = mtvecc.address
function get_stvec() -> xlenbits = read_stvec_utvec(stvecc.address)

function set_mtvec(value : xlenbits) -> unit = {
  let mtv = legalize_tvec(Mk_Mtvec(mtvecc.address), convertInvalidAddr(value));
  mtvecc = tvecc_vector_range_check(setCapAddrChecked(mtvecc, mtv.bits));
  // TODO (CLIC): Need to set mpil etc.
}

function set_stvec(value : xlenbits) -> unit = {
  let stv = legalize_tvec(Mk_Mtvec(stvecc.address), convertInvalidAddr(value));
  stvecc = tvecc_vector_range_check(setCapAddrChecked(stvecc, stv.bits));
  // TODO (CLIC): Need to set mpil etc.
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
  mepcc = setCapAddrChecked(mepcc, legalize_xepc(convertInvalidAddr(value)));
}

function set_sepc(value : xlenbits) -> unit = {
  sepcc = setCapAddrChecked(sepcc, legalize_xepc(convertInvalidAddr(value)));
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
  ddc = setCapAddrChecked(ddc, convertInvalidAddr(value));
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
  csr_name_map(csrno) == "mtidc" | csr_name_map(csrno) == "stidc" | csr_name_map(csrno) == "utidc"

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
