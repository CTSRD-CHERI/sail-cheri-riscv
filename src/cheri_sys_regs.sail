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
  let c = update_d(c, true);
  let c = update_e(c, true);
  c
}

function read_Xcheri_CSR(csr : csreg) -> option(xlenbits) = {
  let res : option(xlenbits) =
  match csr {
    0x8C0 => Some(uccsr.bits()),
    0x9C0 => Some(sccsr.bits()),
    0xBC0 => Some(mccsr.bits()),
    _     => None()
  };
  res
}

function write_Xcheri_CSR(csr: csreg, value : xlenbits) -> bool = {
  let res : option(xlenbits) =
  match csr {
    0x8C0 => { uccsr = legalize_ccsr(uccsr, value); Some(uccsr.bits()) },
    0x9C0 => { sccsr = legalize_ccsr(sccsr, value); Some(sccsr.bits()) },
    0xBC0 => { mccsr = legalize_ccsr(mccsr, value); Some(mccsr.bits()) },
    _     => None()
  };
  match res {
    Some(v) => { print_reg("CSR " ^ BitStr(csr) ^ " <- " ^ BitStr(v) ^ " (input: " ^ BitStr(value) ^ ")");
                 true },
    None()  => false
  }
}

function is_XCheri_CSR_defined(csr : bits(12), p : Privilege) -> bool =
  match csr {
    0x8C0 => haveUsrMode(),                                    // uccsr
    0x9C0 => haveSupMode() & (p == Machine | p == Supervisor), // sccsr
    0xBC0 => p == Machine | p == Supervisor,                   // mccsr
    _     => false
  }

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
