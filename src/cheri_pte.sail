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

/* PTE attributes, permission checks and updates */

type pteAttribs = bits(8)

bitfield PTE_Bits : pteAttribs = {
  D : 7,
  A : 6,
  G : 5,
  U : 4,
  X : 3,
  W : 2,
  R : 1,
  V : 0
}

/*
 * Reserved PTE bits used by extensions on RV64.
 *
 * For capability store the behaviors are as follows.
 *
 *   CW  CD  Action
 *
 *    0   X    Trap on tagged capability store
 *    1   0    CAS the PTE to CW=1, CD=1 (i.e., set both bits) or trap
 *    1   1    Permit tagged capability store
 *
 * The CW/CD pair is akin to Sv{32,48,...}'s W/D bits.
 *
 * The CW=1 CD=0 behavior is described as a CAS (and not an AMO OR) of the PTE
 * to close race conditions, much as with W and D.  Should the TLB have this
 * state cached and then observe a CW=1 CD=1 PTE, no PTE write is necessary.
 * On the other hand, if CW=0 is observed, the store operation must trap.
 *
 * The intended semantics for capability loads are as follows.
 *
 *   CR  CR_Trap CR_Gen Action
 *
 *    0     0      0    Capability loads strip tags
 *    0     1      0    Capability loads trap (on set tag)
 *    0     X      1    [Reserved]
 *
 *    1     0      0    Capability loads succeed: no traps or tag clearing
 *    1     0      1    [Reserved]
 *    1     1      G    Capability loads trap if G mismatches sccsr.[su]gclg,
 *                      where the compared bit is keyed off of this PTE's U.
 *
 * Sv32: There are no extension bits available, so we hard-code the result to
 * CW=1 CR=1 CD=1 CR_Trap=0 CR_Gen=0
 */
type extPte = bits(10)

bitfield Ext_PTE_Bits : extPte = {
  CapWrite     : 9, /* Permit capability stores */
  CapRead      : 8, /* Permit capability loads */
  CapDirty     : 7, /* Capability Dirty flag */
  CapRead_Trap : 6, /* Trap on capability loads; see above table */
  CapRead_Gen  : 5, /* When load-cap gens. are in use, the "local" gen. bit */
}

/*
 * CapWrite     = 1,
 * CapRead      = 1,
 * CapDirty     = 1,
 * CapRead_Trap = 0,
 * CapRead_Gen  = 0,
 * bits 0 .. 4  = 0
 */
let default_sv32_ext_pte : extPte = 0b1110000000

function isPTEPtr(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.R() == 0b0 & a.W() == 0b0 & a.X() == 0b0
}

function isInvalidPTE(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  let e = Mk_Ext_PTE_Bits(ext);
  a.V() == 0b0 | (a.W() == 0b1 & a.R() == 0b0) |
  (e.CapRead() == 0b0 & e.CapRead_Gen() == 0b1) |
  (e.CapRead() == 0b1 & e.CapRead_Gen() == 0b1 & e.CapRead_Trap() == 0b0)
}

union PTE_Check = {
  PTE_Check_Success : ext_ptw,
  PTE_Check_Failure : (ext_ptw, ext_ptw_fail)
}

/* Gate Cap-transporting stores on the CapWrite PTE bit */
val checkPTEPermission_SC : (Ext_PTE_Bits, ext_ptw) -> PTE_Check effect { rreg }
function checkPTEPermission_SC(e, ext_ptw) = {
  if   e.CapWrite() == 0b1
  then PTE_Check_Success(ext_ptw)
  else PTE_Check_Failure(ext_ptw, EPTWF_CAP_ERR)
}

/*
 * Assuming we're allowed to load from this page, modulate our cap response
 */
val checkPTEPermission_LC : (PTE_Bits, Ext_PTE_Bits, ext_ptw) -> PTE_Check effect { escape, rreg }
function checkPTEPermission_LC(p, e, ext_ptw) =
  match (e.CapRead(), e.CapRead_Trap(), e.CapRead_Gen()) {
    (0b0, 0b0, 0b0)  => PTE_Check_Success(ext_ptw_lc_join(ext_ptw, PTW_LC_CLEAR)), /* Clear tag for "unmodified" no-LC case */
    (0b0, 0b1, 0b0)  => PTE_Check_Success(ext_ptw_lc_join(ext_ptw, PTW_LC_TRAP)),  /* Trap on tag load for "modified" no-LC case */
    (0b0, _  , 0b1)  => internal_error("Bad PTE not caught by isInvalidPTE"),
    (0b1, 0b0, 0b0)  => PTE_Check_Success(ext_ptw_lc_join(ext_ptw, PTW_LC_OK)), /* Unmodified LC case: go ahead */
    (0b1, 0b0, 0b1)  => internal_error("Bad PTE not caught by isInvalidPTE"),
    (0b1, 0b1, lclg) => {
      /* Compare local CLG against the pte.U-selected, not mode-selected, global CLG bit */
      let gclg : bits(1) = if p.U() == 0b1 then sccsr.ugclg() else sccsr.sgclg();
      let ptwl = if lclg == gclg then PTW_LC_OK else PTW_LC_TRAP;
      PTE_Check_Success(ext_ptw_lc_join(ext_ptw, ptwl))
    }
  }

function checkPTEPermission(ac : AccessType(ext_access_type), priv : Privilege, mxr : bool, do_sum : bool, p : PTE_Bits, ext : extPte, ext_ptw : ext_ptw) -> PTE_Check = {
  /*
   * Although in many cases MXR doesn't make sense for capabilities, we honour
   * it for three reasons:
   *
   * 1. It provides uniformity rather than giving strange and surprising edge cases.
   *
   * 2. The tag-dependence of stores is achieved by passing Data in for untagged
   *    capabilities. Thus, not honouring MXR for capabilities would result in
   *    differences in whether MXR had an effect based on the tag.
   *
   * 3. It's simpler to implement yet still safe (LC is unaffected by MXR).
   */
  let succ : bool =
  match (ac, priv) {
    (Read(_),      User)       => p.U() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Write(_),     User)       => p.U() == 0b1 & p.W() == 0b1,
    (ReadWrite(_), User)       => p.U() == 0b1 & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Execute(),    User)       => p.U() == 0b1 & p.X() == 0b1,

    (Read(_),      Supervisor) => (p.U() == 0b0 | do_sum) & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Write(_),     Supervisor) => (p.U() == 0b0 | do_sum) & p.W() == 0b1,
    (ReadWrite(_), Supervisor) => (p.U() == 0b0 | do_sum) & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Execute(),    Supervisor) => p.U() == 0b0 & p.X() == 0b1,

    (_,            Machine)    => internal_error("m-mode mem perm check")
  };

  let res =
    if   succ
    then PTE_Check_Success(ext_ptw)
    else PTE_Check_Failure(ext_ptw, EPTWF_NO_PERM);

  let e = Mk_Ext_PTE_Bits(ext);

  /* Store side */
  let res : PTE_Check = match res {
    PTE_Check_Failure(_, _) => res,
    PTE_Check_Success(ext_ptw) => match ac {
      Execute()          => res,
      Read(_)            => res,
      Write(Data)        => res,
      ReadWrite(_, Data) => res,

      Write(Cap)         => checkPTEPermission_SC(e, ext_ptw),
      ReadWrite(_, Cap)  => checkPTEPermission_SC(e, ext_ptw)
    }
  };

  /* Load side */
  let res : PTE_Check = match res {
    PTE_Check_Failure(_, _) => res,
    PTE_Check_Success(ext_ptw) => match ac {
      Execute()          => res,
      Read(Data)         => res,
      Write(_)           => res,
      ReadWrite(Data, _) => res,

      Read(Cap)          => checkPTEPermission_LC(p, e, ext_ptw),
      ReadWrite(Cap, _)  => checkPTEPermission_LC(p, e, ext_ptw)
    }
  };

  res
}

function update_PTE_Bits(p : PTE_Bits, a : AccessType(ext_access_type), ext : extPte) -> option((PTE_Bits, extPte)) = {
  // dirty bit
  let update_d = p.D() == 0b0 & (match a {
                                  Execute()       => false,
                                  Read(_)         => false,
                                  Write(_)        => true,
                                  ReadWrite(_, _) => true
                                });

  // accessed bit
  let update_a = p.A() == 0b0;

  let pte_ext = Mk_Ext_PTE_Bits(ext);

  // store cap bits
  let update_cd = pte_ext.CapWrite() == 0b1 &
                  pte_ext.CapDirty() == 0b0 &
                  (match a {
                    Write(Cap)        => true,
                    ReadWrite(_, Cap) => true,
                    _                 => false
                  });

  if update_d | update_a | update_cd then {
    let np = update_A(p, 0b1);
    let np = if update_d then update_D(np, 0b1) else np;
    let npte_ext = if update_cd then update_CapDirty(pte_ext, 0b1) else pte_ext;
    Some(np, npte_ext.bits())
  } else None()
}
