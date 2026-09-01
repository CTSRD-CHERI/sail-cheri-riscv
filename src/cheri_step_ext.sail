/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function ext_cheri_reset() -> unit = {
  PCC = root_cap;
  nextPCC = root_cap;
  ddc = root_cap;

  // The address bits may have been initialised by the non-CHERI reset to a non-zero value.
  stvec_y = {root_cap with address = stvec.bits};
  sscratch_y = {sscratch_y with tag = false, address = sscratch} ;
  sepc_y = root_cap;
  mtid_y = {mtid_y with tag = false};
  stid_y = {stid_y with tag = false};
  utid_y = {utid_y with tag = false};

  mtvec_y = {root_cap with address = mtvec.bits};
  mscratch_y = {mscratch_y with tag = false, address = mscratch} ;
  mepc_y = root_cap;

  // dpcc = {dpcc with tag = false} ;
  // dscratch0c = {dscratch0c with tag = false};
  // dscratch1c = {dscratch1c with tag = false};
  // dddc = {dddc with tag = false};
  // drootc = root_cap;

  //x1 = {x1 with tag = false};
  //x2 = {x2 with tag = false};
  //x3 = {x3 with tag = false};
  //x4 = {x4 with tag = false};
  //x5 = {x5 with tag = false};
  //x6 = {x6 with tag = false};
  //x7 = {x7 with tag = false};
  //x8 = {x8 with tag = false};
  //x9 = {x9 with tag = false};
  //x10 = {x10 with tag = false};
  //x11 = {x11 with tag = false};
  //x12 = {x12 with tag = false};
  //x13 = {x13 with tag = false};
  //x14 = {x14 with tag = false};
  //x15 = {x15 with tag = false};
  //x16 = {x16 with tag = false};
  //x17 = {x17 with tag = false};
  //x18 = {x18 with tag = false};
  //x19 = {x19 with tag = false};
  //x20 = {x20 with tag = false};
  //x21 = {x21 with tag = false};
  //x22 = {x22 with tag = false};
  //x23 = {x23 with tag = false};
  //x24 = {x24 with tag = false};
  //x25 = {x25 with tag = false};
  //x26 = {x26 with tag = false};
  //x27 = {x27 with tag = false};
  //x28 = {x28 with tag = false};
  //x29 = {x29 with tag = false};
  //x30 = {x30 with tag = false};
  //x31 = {x31 with tag = false};

  if (platform_get_rvfi_dii()) then {
    x1  = root_cap;
    x2  = root_cap;
    x3  = root_cap;
    x4  = root_cap;
    x5  = root_cap;
    x6  = root_cap;
    x7  = root_cap;
    x8  = root_cap;
    x9  = root_cap;
    x10 = root_cap;
    x11 = root_cap;
    x12 = root_cap;
    x13 = root_cap;
    x14 = root_cap;
    x15 = root_cap;
    x16 = root_cap;
    x17 = root_cap;
    x18 = root_cap;
    x19 = root_cap;
    x20 = root_cap;
    x21 = root_cap;
    x22 = root_cap;
    x23 = root_cap;
    x24 = root_cap;
    x25 = root_cap;
    x26 = root_cap;
    x27 = root_cap;
    x28 = root_cap;
    x29 = root_cap;
    x30 = root_cap;
    x31 = root_cap;
  }
}

function ext_reset_misa() -> unit = ()

function ext_fetch_mem_read_hi(paddr : physaddr, pbmt : PBMT) -> MemoryOpResult(half) = mem_read(Execute(), pbmt, paddr, 2, false, false, false)
function ext_fetch_mem_read_lo(paddr : physaddr, pbmt : PBMT) -> MemoryOpResult(half) = mem_read(Execute(), pbmt, paddr, 2, false, false, false)

// Print an instruction we are executing. For CHERI we print the mode too.
function ext_print_instr forall 'n, 'n in {16, 32} . (
  step_no : int, ast : ast, opcode : bits('n)
) -> unit = {
  if get_config_print_instr()
  then {
    let cheri_mode : string = match effective_cheri_mode() {
      CapPtrMode => "CapPtrMode",
      IntPtrMode  => "Integer",
    };
    print_instr(
      "[" ^ dec_str(step_no) ^ "] [" ^ to_str(cur_privilege()) ^ "," ^ cheri_mode ^ "]: " ^
      BitStr(PC) ^ " (" ^ BitStr(opcode) ^ ") " ^ to_str(ast)
    );
  };
}
