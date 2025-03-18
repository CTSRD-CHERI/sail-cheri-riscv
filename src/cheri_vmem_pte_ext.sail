/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function pte_permission_ok(
  ac      : AccessType(ext_access_type),
  priv    : Privilege,
  mxr     : bool,
  do_sum  : bool,
  pte     : PTE_Flags,
  ext     : option(PTE_Ext), // None() for Sv32.
  ext_ptw : ext_ptw,
) -> (bool, ext_ptw) = {
  let non_cheri_page_fault = not(pte_rwxu_permission_ok(ac, priv, mxr, do_sum, pte));

  var cheri_page_fault : bool = false;
  var tagged_load_behaviour = TaggedLoadOk;

  // CHERI PTE features only supported on RV64.
  match ext {
    Some(ext) => {
      if isTaggedWrite(ac) &
        ext[CW] == 0b0 &
        (ext[CRG] == 0b0 | not(plat_enable_dirty_update())) then {
        cheri_page_fault = true;
      } else if isTaggedRead(ac) then {
        match (ext[CW], ext[CRG]) {
          // Clear loaded tag.
          (0b0, _) => tagged_load_behaviour = TaggedLoadClear,
          // Page fault, or page fault if tag set.
          (0b1, crg) if crg == mstatus[UCRG] => {
            if sys_cheri_pte_crg_exception_check_tag() then {
              tagged_load_behaviour = TaggedLoadTrap;
            } else {
              cheri_page_fault = true;
            }
          },
          (0b1, _) => (),
        }
      }
    },
    None() => (),
  };

  let ext_ptw = { ext_ptw with tagged_load_behaviour = tagged_load_behaviour };

  match (cheri_page_fault, non_cheri_page_fault) {
    (true, true)   => (false, { ext_ptw with cheri_page_fault = PageFault_Both }),
    (true, false)  => (false, { ext_ptw with cheri_page_fault = PageFault_Cheri }),
    (false, true)  => (false, { ext_ptw with cheri_page_fault = PageFault_NonCheri }),
    (false, false) => (true, ext_ptw),
  }
}

// Update a PTE's A/D bits and write it to memory. This returns
//
// * Ok(Some(pte)) if a write was needed and was successful. pte is the new value.
// * Ok(None()) if no write was needed.
// * Err(e) if a write was needed but there was an error.
//

// This needs a separate type declaration due to this possible bug:
// https://github.com/rems-project/sail/issues/984
val updated_cheri_pte_bits : forall 'pte_size, 'pte_size in {32, 64} . (bits('pte_size), AccessType(ext_access_type)) -> option(bits('pte_size))
function updated_cheri_pte_bits(pte, ac) =
  match ext_bits_of_PTE(pte) {
    Some(ext) if isTaggedWrite(ac) & ext[CW] == 0b0 & ext[CRG] == 0b1 => {
      // CHERI PTEs & PTE ext bits only exist with 64-bit PTEs.
      assert('pte_size == 64);
      Some([pte with 63 .. 54 = [ext with CW = 0b1, CRG = mstatus[UCRG]].bits])
    },
    _ => None(),
  }

function update_pte forall 'pte_width, 'pte_width in {4, 8} . (
  pte_width : int('pte_width),
  pteAddr   : physaddr,
  pte       : bits('pte_width * 8),
  ac        : AccessType(ext_access_type),
  ext_ptw   : ext_ptw,
) -> (result(option(bits('pte_width * 8)), PTW_Error), ext_ptw) = {
  // Get the updated PTE, and the fault cause (if there turns out to
  // be one when we try to write it).
  let (pte, fault_cause) : (bits('pte_width * 8), CheriPageFault) = match updated_pte_bits(pte, ac) {
    Some(pte) => match updated_cheri_pte_bits(pte, ac) {
      Some(pte) => (pte, PageFault_Both),
      None() => (pte, PageFault_NonCheri),
    },
    None() => match updated_cheri_pte_bits(pte, ac) {
      Some(pte) => (pte, PageFault_Cheri),
      None() => return (Ok(None()), ext_ptw), // No updates needed.
    },
  };

  if not(plat_enable_dirty_update()) then {
    (Err(PTW_PTE_Update()), {ext_ptw with cheri_page_fault = fault_cause})
  } else {
    match write_pte(pteAddr, 'pte_width, pte) {
      Ok(_) => (Ok(Some(pte)), ext_ptw),
      Err(_) => (Err(PTW_Access()), {ext_ptw with cheri_page_fault = fault_cause}),
    }
  }
}
