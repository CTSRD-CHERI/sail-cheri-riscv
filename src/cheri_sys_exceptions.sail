/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* CHERI exception model */

type ext_exception = unit

/*
 * On traps, EPCC comes to hold PCC verbatim.
 */
function handle_trap_extension(p : Privilege, pc : xlenbits, u : option(unit)) -> unit = {
  if not(debug_mode_active) then {
    let (_, newXepcc) = setCapAddr(PCC, pc);
    match p {
      Machine => {
        mepcc = newXepcc;
      },
      Supervisor => {
        sepcc = newXepcc;
      },
      User => internal_error(__FILE__, __LINE__, "N extension not supported"),
    }
  };
}

function handle_nmi_extension(pc : xlenbits, handler_pc : xlenbits) -> unit = {
  // Ignore representability check, since setting address on infinite_cap always succeeds.
  let (_, nmi_pcc) = setCapAddr(infinite_cap, handler_pc);
  set_next_pcc(nmi_pcc);

  // Set MEPCC to PCC as for other traps
  // NMIs always trap into M-mode
  let (_, newXepcc) = setCapAddr(PCC, pc);
  mepcc = newXepcc;
}

/* used for traps and ECALL */
function prepare_trap_vector(p : Privilege, c : Mcause) -> xlenbits = {
  let tvecc : Capability = match p {
                           Machine    => mtvecc,
                           Supervisor => stvecc,
                           User       => internal_error(__FILE__, __LINE__, "N extension not supported"),
                         };

  /* Calculate absolute target address from xtvecc address (offset) and mode, and
     insert it into PCC (with xtvecc metadata) and return it to be inserted into PC.
     Inserting xtvecc directly into PCC would result in incorrect address in PCC. */
  match tvec_addr(Mk_Mtvec(tvecc.address), c) {
    // Note that the representability check for xtvecc.address + 4 * MAX_MCAUSE
    // will have been done when xtvecc is written, so we blindly copy the address
    // in. If it is not representable the xtvecc tag will have already been
    // cleared.
    Some(addr) => { if not(debug_mode_active) then set_next_pcc({tvecc with address=addr}); addr },
    None()     => internal_error(__FILE__, __LINE__, "Invalid tvec mode")
  }
}

val prepare_clic_xret_vectored_target : (Privilege) -> xlenbits

function prepare_xret_target(p : Privilege) -> xlenbits = {
  if inSmclicMode() & get_xcause(p)[Xinhv] == 0b1
  // TODO (CLIC): CHERI integration.
  then prepare_clic_xret_vectored_target(p)
  else {
    /* Similar to prepare_trap_vector above we need to return the absolute address
      destined for PC, rather than the offset (architecutral PC) */
    let epcc : Capability = match p {
                              Machine    => mepcc,
                              Supervisor => sepcc,
                              User       => internal_error(__FILE__, __LINE__, "N extension not supported"),
                            };

    let epcc = legalize_epcc(epcc);

    set_next_pcc(unsealCap(epcc));
    epcc.address
  }
}
