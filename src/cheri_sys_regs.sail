/* CHERI system CSRs */

/* Capability control csr */

bitfield ccsr : xlenbits = {
  cap_idx : 15 .. 10,
  cause   :  9 .. 5, /* cap cause */
  d       :  1,      /* dirty  */
  e       :  0       /* enable */
}

register mccsr : ccsr
register sccsr : ccsr
register uccsr : ccsr

/* access to CCSRs */

// for now, use a single privilege-independent legalizer
function legalize_ccsr(c : ccsr, v : xlenbits) -> ccsr = {
  // write only the defined bits, leaving the other bits untouched
  // Technically, WPRI does not need a legalizer, since software is
  // assumed to legalize; so we could remove this function.
  let v = Mk_ccsr(v);
  let c = update_cap_idx(c, v.cap_idx());
  let c = update_cause(c, v.cause());
  /* For now these bits are not really supported so hardwired to true */
  let c = update_d(c, 0b1);
  let c = update_e(c, 0b1);
  c
}

// XXX these are currently disabled due to sail bug when compiling C
//mapping clause csr_name_map = 0x8c0 <-> "uccsr"
//mapping clause csr_name_map = 0x9c0 <-> "sccsr"
//mapping clause csr_name_map = 0xBc0 <-> "mccsr"

function clause ext_read_CSR (0x8C0) = Some(uccsr.bits())
function clause ext_read_CSR (0x9C0) = Some(sccsr.bits())
function clause ext_read_CSR (0xBC0) = Some(mccsr.bits())

function clause ext_write_CSR (0x8C0, value) = { uccsr = legalize_ccsr(uccsr, value); Some(uccsr.bits()) }
function clause ext_write_CSR (0x9C0, value) = { sccsr = legalize_ccsr(sccsr, value); Some(sccsr.bits()) }
function clause ext_write_CSR (0xBC0, value) = { mccsr = legalize_ccsr(mccsr, value); Some(mccsr.bits()) }

function clause ext_is_CSR_defined (0x8C0, p) = haveUsrMode()  // uccsr
function clause ext_is_CSR_defined (0x9C0, p) = haveSupMode() & (p == Machine | p == Supervisor) // sccsr
function clause ext_is_CSR_defined (0xBC0, p) = p == Machine | p == Supervisor // mccsr

/* Other architectural registers */

register PCC       : Capability
register nextPCC   : Capability
register DDC       : Capability

register UTCC      : Capability
register UTDC      : Capability
register UScratchC : Capability
register UEPCC     : Capability
register STCC      : Capability
register STDC      : Capability
register SScratchC : Capability
register SEPCC     : Capability
register MTCC      : Capability
register MTDC      : Capability
register MScratchC : Capability
register MEPCC     : Capability

/* Cheri PCC helpers */

function min_instruction_bytes () -> CapAddrInt = {
  if   (~ (sys_enable_writable_misa ())) & (~ (sys_enable_rvc ()))
  then 4  /* RVC is hardwired to be disabled */
  else 2  /* RVC is active or it could become active */
}

/* Checking whether the Xcheri extension is enabled */

function haveXcheri () -> bool =
  /* This is a necessary but not sufficient condition, but should do for now. */
  misa.X() == 0b1


function legalize_tcc(o : Capability, v : Capability) -> Capability = {
  new_tvec = getCapOffsetBits(v);
  legalized_tvec = legalize_tvec(Mk_Mtvec(getCapOffsetBits(o)), new_tvec);
  setCapOffsetOrNull(v, legalized_tvec.bits())
}

function legalize_epcc (v : Capability) -> Capability = {
  setCapOffsetOrNull(v, legalize_xepc(getCapOffsetBits(v)))
}
