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

/* Reserved PTE bits could be used by extensions on RV64.  There are
 * no such available bits on RV32, so these bits will be zeros on RV32.
 */
type extPte = bits(10)

bitfield Ext_PTE_Bits : extPte = {
  LoadCap  : 9,
  StoreCap : 8,
}

function isPTEPtr(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.R() == false & a.W() == false & a.X() == false
}

function isInvalidPTE(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.V() == false | (a.W() == true & a.R() == false)
}

union PTE_Check = {
  PTE_Check_Success : unit,
  PTE_Check_Failure : unit,
  PTE_Check_Ext     : ext_pte_error
}

function to_pte_check(b : bool) -> PTE_Check =
  if b then PTE_Check_Success() else PTE_Check_Failure(())

function checkPTEPermission(ac : AccessType(ext_access_type), priv : Privilege, mxr : bool, do_sum : bool, p : PTE_Bits, ext : extPte) -> PTE_Check = {
  match (ac, priv) {
    (Read(Data),      User)       => to_pte_check(p.U() == true & (p.R() == true | (p.X() == true & mxr))),
    (Write(Data),     User)       => to_pte_check(p.U() == true & p.W() == true),
    (ReadWrite(Data), User)       => to_pte_check(p.U() == true & p.W() == true & (p.R() == true | (p.X() == true & mxr))),
    (Execute(),       User)       => to_pte_check(p.U() == true & p.X() == true),

    (Read(Data),      Supervisor) => to_pte_check((p.U() == false | do_sum) & (p.R() == true | (p.X() == true & mxr))),
    (Write(Data),     Supervisor) => to_pte_check((p.U() == false | do_sum) & p.W() == true),
    (ReadWrite(Data), Supervisor) => to_pte_check((p.U() == false | do_sum) & p.W() == true & (p.R() == true | (p.X() == true & mxr))),
    (Execute(),       Supervisor) => to_pte_check(p.U() == false & p.X() == true),

    (Read(Cap),       User)       => { /* load-cap should probably not be affected by mxr. */
                                       if   p.U() == true & p.R() == true
                                       then {
                                         let  e = Mk_Ext_PTE_Bits(ext);
                                         if   e.LoadCap() == true
                                         then PTE_Check_Success()
                                         else PTE_Check_Ext(PTE_LOAD_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (Write(Cap),      User)       => { if   p.U() == true & p.W() == true
                                       then {
                                         let  e = Mk_Ext_PTE_Bits(ext);
                                         if   e.StoreCap() == true
                                         then PTE_Check_Success()
                                         else PTE_Check_Ext(PTE_STORE_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (ReadWrite(Cap),  User)       => { if   p.U() == true & p.R() == true & p.W() == true
                                       then {
                                         let  e = Mk_Ext_PTE_Bits(ext);
                                         if   e.StoreCap() == true & e.LoadCap() == true
                                         then PTE_Check_Success()
                                         /* return the store error since we should cause an exception */
                                         else PTE_Check_Ext(PTE_STORE_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (Read(Cap),       Supervisor) => { if   (p.U() == false | do_sum) & p.R() == true
                                       then {
                                         let  e = Mk_Ext_PTE_Bits(ext);
                                         if   e.LoadCap() == true
                                         then PTE_Check_Success()
                                         else PTE_Check_Ext(PTE_LOAD_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (Write(Cap),      Supervisor) => { let e = Mk_Ext_PTE_Bits(ext);
                                       if   (p.U() == false | do_sum) & p.W() == true
                                       then {
                                         if   e.StoreCap() == true
                                         then PTE_Check_Success()
                                         else PTE_Check_Ext(PTE_STORE_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (ReadWrite(Cap),  Supervisor) => { let e = Mk_Ext_PTE_Bits(ext);
                                       if   (p.U() == false | do_sum) & p.R() == true & p.W() == true
                                       then {
                                         if   e.StoreCap() == true & e.LoadCap() == true
                                         then PTE_Check_Success()
                                         /* return the store error since we should cause an exception */
                                         else PTE_Check_Ext(PTE_STORE_CAP_ERR)
                                       }
                                       else PTE_Check_Failure()
                                     },

    (_,               Machine)    => internal_error("m-mode mem perm check")
  }
}

function update_PTE_Bits(p : PTE_Bits, a : AccessType(ext_access_type), ext : extPte) -> option((PTE_Bits, extPte)) = {
  let update_d = (a == Write(Data) | a == ReadWrite(Data)) & p.D() == false; // dirty-bit
  let update_a = p.A() == false;                                             // accessed-bit
  if update_d | update_a then {
    let np = update_A(p, true);
    let np = if update_d then update_D(np, true) else np;
    Some(np, ext)
  } else None()
}
