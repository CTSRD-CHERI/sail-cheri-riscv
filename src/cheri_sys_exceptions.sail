/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

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
    None()     => internal_error(__FILE__, __LINE__, "Invalid tvec mode")
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
  legalize_xepc(cap_to_integer_pc(cap))
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
    Machine    => MEPCC = update_cap_with_integer_pc(MEPCC, value),
    Supervisor => SEPCC = update_cap_with_integer_pc(SEPCC, value),
    User       => UEPCC = update_cap_with_integer_pc(UEPCC, value)
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
  cap_to_integer_pc(MTCC)

function get_stvec() -> xlenbits =
  cap_to_integer_pc(STCC)

function get_utvec() -> xlenbits =
  cap_to_integer_pc(UTCC)

function set_mtvec(value : xlenbits) -> xlenbits = {
  let mtv = legalize_tvec(Mk_Mtvec(cap_to_integer_pc(MTCC)), value);
  MTCC = update_cap_with_integer_pc(MTCC, mtv.bits());
  mtv.bits()
}

function set_stvec(value : xlenbits) -> xlenbits = {
  let stv = legalize_tvec(Mk_Mtvec(cap_to_integer_pc(STCC)), value);
  STCC = update_cap_with_integer_pc(STCC, stv.bits());
  stv.bits()
}

function set_utvec(value : xlenbits) -> xlenbits = {
  let utv = legalize_tvec(Mk_Mtvec(cap_to_integer_pc(UTCC)), value);
  UTCC = update_cap_with_integer_pc(UTCC, utv.bits());
  utv.bits()
}
