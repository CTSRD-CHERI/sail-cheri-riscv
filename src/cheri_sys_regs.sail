/* CHERI system CSRs */

/* Capability control csr */

bitfield ccsr : xlenbits = {
  ugclg   :  3,      /* Global Cap Load Gen bit for User pages */
  sgclg   :  2,      /* Global Cap Load Gen bit for System (not User) pages */
  d       :  1,      /* dirty  */
  e       :  0       /* enable */
}

register sccsr : ccsr /* mccsr aliases sccsr */
register uccsr : ccsr

/* access to CCSRs */

function legalize_ccsr(csrp : Privilege, c : ccsr, v : xlenbits) -> ccsr = {
  // write only the defined bits, leaving the other bits untouched
  let v = Mk_ccsr(v);

  let c : ccsr = match csrp {
    User => {
      // No bits defined for uccsr
      c
    },
    _    => {
      let c = update_ugclg(c, v.ugclg());
      let c = update_sgclg(c, v.sgclg());
      c
    }
  };

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
function clause ext_read_CSR (0xBC0) = Some(sccsr.bits())

function clause ext_write_CSR (0x8C0, value) = { uccsr = legalize_ccsr(User, uccsr, value); Some(uccsr.bits()) }
function clause ext_write_CSR (0x9C0, value) = { sccsr = legalize_ccsr(Supervisor, sccsr, value); Some(sccsr.bits()) }
function clause ext_write_CSR (0xBC0, value) = { sccsr = legalize_ccsr(Machine, sccsr, value); Some(sccsr.bits()) }

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
  new_base = getCapBaseBits(v);
  /* Ignore writes that attempt to set unaligned TCC base */
  if new_base[0] != bitzero | new_base[1] != bitzero then
    o /* keep original TCC value */
  else {
    /* legalize new TCC offset (RISC-V tvec) */
    new_tvec = v.address - new_base;
    legalized_tvec = legalize_tvec(Mk_Mtvec(getCapOffsetBits(o)), new_tvec);
    setCapOffsetOrNull(v, legalized_tvec.bits())
  }
}

/*
 * Used during readout (but not assignment!) of ?EPCC registers (CSpecialRW,
 * handle_trap_extension) and not during control transfer
 * (prepare_xret_target).
 *
 * The result is that it is only possible to faithfully read out ?EPCC if
 * either
 *  - misa.C is enabled or
 *  - misa.C is disabled and the EPCC offset is sufficiently aligned
 *
 * If misa.C is held constant, as it almost always will be, between fault and
 * readback, ?EPCC will be faithfully read back, because the alignment will
 * adhere to the requirements of the architecture, which is what legalization
 * is intending to enforce.
 *
 * If neither of those conditions hold, the resulting readout will be a lie; if
 * ?EPCC has additionally been set to be a sentry, then the result will be an
 * untagged lie.
 */
function legalize_epcc (v : Capability) -> Capability = {
  let voffset = getCapOffsetBits(v);
  let legalized = legalize_xepc(voffset);

  if   legalized == voffset
  then v /* avoid possibly attempting to set the offset of a sentry */
  else setCapOffsetOrNull(v, legalized)
}
