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

// If set then loads with CRW=1, CRG!=mstatus[UCRG] will only trap if the
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

// Returned on success and failure from translateAddr().
struct ext_ptw = {
  // Behaviour to apply when tagged capabilities are loaded
  // and we know if they are tagged or not.
  tagged_load_behaviour : TaggedLoadBehaviour,
  // Was there a cheri page fault
  cheri_page_fault : option(CheriPageAccess),
}

let init_ext_ptw : ext_ptw = struct {
  tagged_load_behaviour = TaggedLoadOk,
  cheri_page_fault = None(),
}

/* CHERI exception extensions */

// Extended exception type in main code - used in `ExceptionType::E_Extension`
union ext_exc_type = {
  EXC_CHERI : CapCheckType
}

// Convert from the exception code to the extended
// exception type.
val ext_exc_type_of_bits : exc_code -> ext_exc_type
function ext_exc_type_of_bits(e) =
  match e {
    0x20 => EXC_CHERI (CapCheckType_Inst()),
    0x21 => EXC_CHERI (CapCheckType_Ld()),
    0x22 => EXC_CHERI (CapCheckType_St()),
    0x23 => EXC_CHERI (CapCheckType_Pte(CheriPage_Ld)),
    0x24 => EXC_CHERI (CapCheckType_Pte(CheriPage_St)),
    _ => internal_error(__FILE__, __LINE__, "unknown exception type")
  }

/* CHERI conversion of extension exceptions to integers */
val num_of_ext_exc_type : ext_exc_type -> range(0, xlen - 1)
function num_of_ext_exc_type(e) =
  match e {
    EXC_CHERI(CapCheckType_Inst()) => 32,
    EXC_CHERI(CapCheckType_Ld()) => 33,
    EXC_CHERI(CapCheckType_St()) => 34,
    EXC_CHERI(CapCheckType_Pte(CheriPage_Ld)) => 35,
    EXC_CHERI(CapCheckType_Pte(CheriPage_St)) => 36,
  }

// Convert exception code to extended exception type.
val ext_exc_type_to_bits : ext_exc_type -> exc_code
function ext_exc_type_to_bits(e) =
  to_bits(8, num_of_ext_exc_type(e))

/* CHERI conversion of extension exceptions to strings */
val ext_exc_type_to_str : ext_exc_type -> string
function ext_exc_type_to_str(e) =
  match e {
    EXC_CHERI (checkType) => "CHERI " ^ capchecktype_name(checkType) ^ " fault",
  }

/* CHERI fetch address checks */

type ext_fetch_addr_error = unit

enum bropw_zba_y = {RISCV_YSH1ADDUW, RISCV_YSH2ADDUW, RISCV_YSH3ADDUW, RISCV_YSH4ADDUW}
enum brop_zba_y = {RISCV_YSH1ADD, RISCV_YSH2ADD, RISCV_YSH3ADD, RISCV_YSH4ADD}
