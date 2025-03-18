/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/*
 * Extension for CHERI page table walker
 *
 * We are going to carry around a summary of the PTW walk for data-dependent
 * (well, tag-dependent) behaviors by the instructions.
 */

// If set then loads with CW=1, CRG!=mstatus[UCRG] will only trap if the
// loaded capability tag is set. Otherwise they will always trap.
function sys_cheri_pte_crg_exception_check_tag() -> bool = false

// Behaviour to apply when a capability is loaded with its tag set.
enum TaggedLoadBehaviour = {
   // Loaded tags are allowed.
  TaggedLoadOk,
  // If the loaded value has its tag set then a page
  // fault should be raised.
  TaggedLoadTrap,
  // If the loaded value has its tag set then clear it.
  TaggedLoadClear,
}

enum CheriPageFault = {
  PageFault_NonCheri,
  PageFault_Cheri,
  PageFault_Both,
}

// Returned on success and failure from translateAddr().
struct ext_ptw = {
  // Behaviour to apply when tagged capabilities are loaded
  // and we know if they are tagged or not.
  tagged_load_behaviour : TaggedLoadBehaviour,
  // Was there a cheri page fault (or both?). This is used
  // to set mtval2.
  cheri_page_fault : CheriPageFault,
}

let init_ext_ptw : ext_ptw = struct {
  tagged_load_behaviour = TaggedLoadOk,
  cheri_page_fault = PageFault_NonCheri,
}

/* CHERI exception extensions */

// Extended exception type in main code - used in `ExceptionType::E_Extension`
// There's only one exception code for CHERI exceptions so we need
// no additional information here. This could be `unit` but the code
// is a little clearer with a single entry enum.
$[no_enum_number_conversions]
enum ext_exc_type = {
  EXC_CHERI,
}

// Convert exception code to extended exception type.
val ext_exc_type_to_bits : ext_exc_type -> exc_code
function ext_exc_type_to_bits(e) =
  match e {
    EXC_CHERI => 0x1c,
  }

// Convert from the exception code to the extended
// exception type.
val ext_exc_type_of_bits : exc_code -> ext_exc_type
function ext_exc_type_of_bits(e) =
  match e {
    0x1c => EXC_CHERI,
    _ => internal_error(__FILE__, __LINE__, "unknown exception type")
  }

/* CHERI conversion of extension exceptions to integers */
val num_of_ext_exc_type : ext_exc_type -> range(0, xlen - 1)
function num_of_ext_exc_type(e) =
  match e {
    EXC_CHERI => 28,
  }

/* CHERI conversion of extension exceptions to strings */
val ext_exc_type_to_str : ext_exc_type -> string
function ext_exc_type_to_str(e) =
  match e {
    EXC_CHERI => "cheri",
  }

/* CHERI fetch address checks */
type ext_fetch_addr_error = CapEx
