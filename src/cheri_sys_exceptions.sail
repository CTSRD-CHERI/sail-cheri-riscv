/* CHERI exception model */

type ext_exception = unit

/*
 * On traps, EPCC comes to hold PCC verbatim.  Notably, PCC is not sealed under
 * otype_sentry (contrast, for example, CJALR).
 */
function handle_trap_extension(p : Privilege, pc : xlenbits, u : option(unit)) -> unit = {
  match p {
    Machine => {
      let (representable, mepcc) = setCapAddr(PCC, pc);
      assert(representable, "mepcc should always be representable");
      MEPCC   = mepcc
    },
    Supervisor => {
      let (representable, sepcc) = setCapAddr(PCC, pc);
      assert(representable, "sepcc should always be representable");
      SEPCC   = sepcc
    },
    User => {
      let (representable, uepcc) = setCapAddr(PCC, pc);
      assert(representable, "uepcc should always be representable");
      UEPCC   = uepcc
    }
  }
}

/* used for traps and ECALL */
function prepare_trap_vector(p : Privilege, c : Mcause) -> xlenbits = {
  let tcc : Capability = match p {
                           Machine    => MTCC,
                           Supervisor => STCC,
                           User       => UTCC
                         };

  /* NB we use address, not offset here because even though tvec is the offset
     we want the absolute address to insert in PC. The bottom two bits (mode) should 
     be the same because we enforce aligned tcc base. */
  match tvec_addr(Mk_Mtvec(tcc.address), c) { 
    Some(addr) => { nextPCC = tcc; addr },
    None()     => internal_error("Invalid tvec mode")
  }
}

/*
 * Get the user-visible ?EPC from ?EPCC.  This is not used for control flow,
 * just for reads from (integer) CSRs.
 *
 * See legalize_epcc for a discussion of felicity of readback and note that
 * updating EPC with a sentry installed in EPCC is expected to fail, even if
 * the update does not change the offset.  (However, it would be very unusual
 * for software to ever bring the core into such a state except in testing.)
 */
val get_xret_target : Privilege -> xlenbits effect {rreg}
function get_xret_target(p) = {
  let cap : Capability = match p {
    Machine    => MEPCC,
    Supervisor => SEPCC,
    User       => UEPCC
  };
  legalize_xepc(getCapOffsetBits(cap))
}

/*
 * Upon setting any of the ?EPCC values using the (integer) CSRs, derive the
 * result using the current contents of EPCC.  If that's sealed (esp., a
 * sentry) this will de-tag, which won't work out very well.
 *
 * Legalization is deferred until read.
 */
val set_xret_target : (Privilege, xlenbits) -> xlenbits effect {rreg, wreg}
function set_xret_target(p, value) = {
  match p {
    Machine    => MEPCC = setCapOffsetOrNull(MEPCC, value),
    Supervisor => SEPCC = setCapOffsetOrNull(SEPCC, value),
    User       => UEPCC = setCapOffsetOrNull(UEPCC, value)
  };
  value
}

val prepare_xret_target : (Privilege) -> xlenbits effect {rreg, wreg}
function prepare_xret_target(p) = {
  /* Similar to prepare_trap_vector above we need to return the absolute address
     destined for PC, rather than the offset (architecutral PC) */
  let epcc : Capability = match p {
                            Machine    => MEPCC,
                            Supervisor => SEPCC,
                            User       => UEPCC
                          };

  let epcc = legalize_epcc(epcc);

  /*
   * Sentries unseal on transfer into nextPCC; other sealed types will trap
   * with a seal violation later, when we go to do a fetch from nextPCC.
   */
  let epcc = if epcc.otype == to_bits(cap_otype_width, otype_sentry)
             then unsealCap(epcc)
             else epcc;

  nextPCC = epcc;
  epcc.address
}

/* other trap-related CSRs */

function get_mtvec() -> xlenbits =
  getCapOffsetBits(MTCC)

function get_stvec() -> xlenbits =
  getCapOffsetBits(STCC)

function get_utvec() -> xlenbits =
  getCapOffsetBits(UTCC)

function set_mtvec(value : xlenbits) -> xlenbits = {
  let mtv = legalize_tvec(Mk_Mtvec(getCapOffsetBits(MTCC)), value);
  MTCC = setCapOffsetOrNull(MTCC, mtv.bits());
  mtv.bits()
}

function set_stvec(value : xlenbits) -> xlenbits = {
  let stv = legalize_tvec(Mk_Mtvec(getCapOffsetBits(STCC)), value);
  STCC = setCapOffsetOrNull(STCC, stv.bits());
  stv.bits()
}

function set_utvec(value : xlenbits) -> xlenbits = {
  let utv = legalize_tvec(Mk_Mtvec(getCapOffsetBits(UTCC)), value);
  UTCC = setCapOffsetOrNull(UTCC, utv.bits());
  utv.bits()
}
