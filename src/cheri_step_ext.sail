/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function ext_cheri_reset() -> unit = {
  PCC = infinite_cap;
  nextPCC = infinite_cap;
  ddc = infinite_cap;

  // The address bits may have been initialised by the non-CHERI reset to a non-zero value.
  stvecc = {infinite_cap with address = stvec.bits};
  stdc = {stdc with tag = false, address = zeros()} ;
  sscratchc = {sscratchc with tag = false, address = sscratch} ;
  sepcc = infinite_cap;
  mtidc = {mtidc with tag = false};
  stidc = {stidc with tag = false};
  utidc = {utidc with tag = false};

  mtvecc = {infinite_cap with address = mtvec.bits};
  mtdc = {mtdc with tag = false, address = zeros()} ;
  mscratchc = {mscratchc with tag = false, address = mscratch} ;
  mepcc = infinite_cap;

  dpcc = {dpcc with tag = false} ;
  dscratch0c = {dscratch0c with tag = false};
  dscratch1c = {dscratch1c with tag = false};
  dddc = {dddc with tag = false};
  dinfc = infinite_cap;

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
}

function ext_cheri_reset_misa() -> unit = {
  // set misa.X to indicate the presence of a non-standard extension.
  misa[X] = 0b1;
}

//function ext_fetch_hook(f : FetchResult) -> FetchResult = f

function ext_fetch_mem_read_hi(paddr : xlenbits, pbmt : PBMT) -> MemoryOpResult(half) = mem_read(Execute(), pbmt, paddr, 2, false, false, false)
function ext_fetch_mem_read_lo(paddr : xlenbits, pbmt : PBMT) -> MemoryOpResult(half) = mem_read(Execute(), pbmt, paddr, 2, false, false, false)

//function ext_pre_step_hook()  -> unit = ()
//function ext_post_step_hook() -> unit = ()

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
