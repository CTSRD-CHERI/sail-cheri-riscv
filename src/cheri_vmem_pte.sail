/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// ****************************************************************
// PTE (Page Table Entry) in PTN (Page Table Node)

// PTE      MSBs      PPNs      RSW    BITs
// Sv32      -       31..10    9..8    7..0
// Sv39    63..54    53..10    9..8    7..0
// Sv48    63..54    53..10    9..8    7..0

// MSBs of PTE are reserved for RV64 extensions.
// There are not available bits on RV32, so these bits will be zeros on RV32.

type pte_flags_bits = bits(8)

/* Reserved PTE bits could be used by extensions on RV64.  There are
 * no such available bits on RV32, so these bits will be zeros on RV32.
 */
type pte_ext_bits = bits(10)

bitfield PTE_Ext : pte_ext_bits = {
  N         : 9,      /* NAPOT page table entry */
  PBMT      : 8 .. 7, /* Page based memory types */
  reserved  : 6 .. 0
}

/*
 * CapWrite     = 1,
 * CapRead      = 1,
 * bits 0 .. 7  = 0
 */
// TODO:  Update Zcheri_pte when the spec is finalized.
// let default_sv32_ext_pte : pte_ext_bits = 0b1100000000
let default_sv32_ext_pte : pte_ext_bits = 0b0000000000

// PRIVATE: extract msbs of PTE above the PPN
function ext_bits_of_PTE(sv_params : SV_Params, pte : bits(64)) -> PTE_Ext = {
  Mk_PTE_Ext(if sv_params.log_pte_size_bytes == 3 then pte[63 .. 54] else default_sv32_ext_pte)
}

// PRIVATE: extract PPNs of PTE
function PPNs_of_PTE(sv_params : SV_Params, pte : bits(64)) -> bits(64) = {
  let mask : bits(64) = zero_extend(ones(sv_params.pte_PPNs_size_bits));
  (pte >> sv_params.pte_PPNs_lsb_index) & mask
}

// PRIVATE: 8 LSBs of PTEs in Sv32, Sv39, Sv48 and Sv57
bitfield PTE_Flags : pte_flags_bits = {
  D : 7,    // dirty
  A : 6,    // accessed
  G : 5,    // global
  U : 4,    // User
  X : 3,    // Execute permission
  W : 2,    // Write permission
  R : 1,    // Read permission
  V : 0     // Valid
}

// TODO:  Make these configurable.
function hasSvnapot() -> bool = false
function hasSvpmbt() -> bool = true

// PRIVATE: check if a PTE is a pointer to next level (non-leaf)
function pte_is_ptr(pte_flags : PTE_Flags) -> bool = (pte_flags[X] == 0b0)
                                                      & (pte_flags[W] == 0b0)
                                                      & (pte_flags[R] == 0b0)


// PRIVATE: check if a PTE is valid
function pte_is_invalid(pte_flags : PTE_Flags, pte_ext : PTE_Ext) -> bool =
    pte_flags[V] == 0b0
  | (pte_flags[W] == 0b1 & pte_flags[R] == 0b0)
  | (pte_ext[N] != 0b0 & not(hasSvnapot()))
  | (pte_ext[PBMT] != zeros() & not(hasSvpmbt()))
  | pte_ext[reserved] != zeros()

// ----------------
// Check access permissions in PTE

// For (non-standard) extensions: this function gets the extension-available bits
// of the PTE in pte_ext_bits, and the accumulated information of the page-table-walk
// in ext_ptw. It should return the updated ext_ptw in both success and failure cases.

union PTE_Check = {
  PTE_Check_Success : ext_ptw,
  PTE_Check_Failure : (ext_ptw, ext_ptw_fail)
}

// PRIVATE
function check_PTE_permission(ac        : AccessType(ext_access_type),
                              priv      : Privilege,
                              mxr       : bool,
                              do_sum    : bool,
                              pte_flags : PTE_Flags,
                              ext       : PTE_Ext,
                              ext_ptw   : ext_ptw) -> PTE_Check = {
  let pte_U = pte_flags[U];
  let pte_R = pte_flags[R];
  let pte_W = pte_flags[W];
  let pte_X = pte_flags[X];
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
  let success : bool =
    match (ac, priv) {
      (Read(_),         User)       => (pte_U == 0b1)
                                       & ((pte_R == 0b1)
                                          | ((pte_X == 0b1 & mxr))),
      (Write(_),        User)       => (pte_U == 0b1) & (pte_W == 0b1),
      (ReadWrite(_, _), User)       => (pte_U == 0b1)
                                       & (pte_W == 0b1)
                                       & ((pte_R == 0b1) | ((pte_X == 0b1) & mxr)),
      (Execute(),       User)       => (pte_U == 0b1) & (pte_X == 0b1),
      (Read(_),         Supervisor) => ((pte_U == 0b0) | do_sum)
                                       & ((pte_R == 0b1) | ((pte_X == 0b1) & mxr)),
      (Write(_),        Supervisor) => ((pte_U == 0b0) | do_sum)
                                       & (pte_W == 0b1),
      (ReadWrite(_, _), Supervisor) => ((pte_U == 0b0) | do_sum)
                                       & (pte_W == 0b1)
                                       & ((pte_R == 0b1)
                                          | ((pte_X == 0b1) & mxr)),
      (Execute(),       Supervisor) => (pte_U == 0b0) & (pte_X == 0b1),
      (_,               Machine)    => internal_error(__FILE__, __LINE__,
                                                      "m-mode mem perm check")};

  // TODO:  Update Zcheri_pte when the spec is finalized.
  // let ptw_lc = if ext[CapRead]  == 0b1 then PTW_LC_OK else PTW_LC_CLEAR;
  // let ptw_sc = if ext[CapWrite] == 0b1 then PTW_SC_OK else PTW_SC_TRAP;
  let ptw_lc = PTW_LC_OK;
  let ptw_sc = PTW_SC_OK;
  let (succ, ext_ptw') : (bool, ext_ptw) =
  match (success, ac) {
    /* Base translation exceptions take priority over CHERI exceptions */
    (false, _)                     => (false, init_ext_ptw),

    (true,  Read(Cap))             => (true, ext_ptw_lc_join(ext_ptw, ptw_lc)),
    (true,  Write(Cap))            => (true, ext_ptw_sc_join(ext_ptw, ptw_sc)),
    (true,  ReadWrite(Data, Cap))  => (true, ext_ptw_sc_join(ext_ptw, ptw_sc)),
    (true,  ReadWrite(Cap, Data))  => (true, ext_ptw_lc_join(ext_ptw, ptw_lc)),
    (true,  ReadWrite(Cap, Cap))   => (true, ext_ptw_sc_join(ext_ptw_lc_join(ext_ptw, ptw_lc), ptw_sc)),

    (true,  Read(Data))            => (true, ext_ptw),
    (true,  Write(Data))           => (true, ext_ptw),
    (true,  ReadWrite(Data, Data)) => (true, ext_ptw),
    (true,  Execute())             => (true, ext_ptw)
  };

  if succ
  then PTE_Check_Success(ext_ptw')
  else PTE_Check_Failure(ext_ptw', if ext_ptw'.ptw_sc == PTW_SC_TRAP then EPTWF_CAP_ERR else EPTWF_NO_PERM)
}

// Update PTE bits if needed; return new PTE if updated
// PRIVATE
function update_PTE_Bits(sv_params : SV_Params,
                         pte       : bits(64),
                         a         : AccessType(ext_access_type))
                        -> option(bits(64)) = {
  let pte_flags = Mk_PTE_Flags(pte [7 .. 0]);

  // Update 'dirty' bit?
  let update_d : bool = (pte_flags[D] == 0b0)
                        & (match a {
                             Execute()       => false,
                             Read(_)          => false,
                             Write(_)        => true,
                             ReadWrite(_, _) => true
                           });
  // Update 'accessed'-bit?
  let update_a = (pte_flags[A] == 0b0);

  if update_d | update_a then {
    let pte_flags = [pte_flags with
                      A = 0b1,
                      D = (if update_d then 0b1 else pte_flags[D])];
    Some(pte[63 .. 8] @ pte_flags.bits())
  }
  else
    None()
}
