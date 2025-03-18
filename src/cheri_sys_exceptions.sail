/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* CHERI exception model */

// Extra exception info passed to handle_trap_extension. We use this
// to store the mtval2 value.
type ext_exception = Tval2

mapping cheri_page_fault_code : CheriPageFault <-> bits(4) = {
  PageFault_NonCheri <-> 0x0,
  PageFault_Cheri <-> 0x1,
  PageFault_Both <-> 0x2,
}

// Translate PTW extra information into extra exception information (passed
// to handle_trap_extension()).
function ext_ptw_exception_info(ext_ptw : ext_ptw) -> ext_exception =
  Mk_Tval2(zero_extend(cheri_page_fault_code(ext_ptw.cheri_page_fault)))

// * When a trap is taken into X-mode, Xepcc is written with the pcc including the virtual
//   address of the instruction that was interrupted or that encountered an exception.
// * When a CHERI fault, or CHERI PTE page fault, is taken, Xtval2 is written
//   with additional CHERI-specific exception information; Xtval2 is written
//   to zero for all other exceptions (except hypervisor which isn't supported yet).
//
function handle_trap_extension(p : Privilege, pc : xlenbits, ext : option(Tval2)) -> unit = {
  if not(debug_mode_active) then {
    let (_, newXepcc) = setCapAddr(PCC, pc);
    let xtval2 : Tval2 = match ext {
      Some(value) => value,
      None() => Mk_Tval2(zeros()),
    };
    match p {
      Machine => {
        set_mepcc(newXepcc);
        mtval2 = xtval2;
      },
      Supervisor => {
        set_sepcc(newXepcc);
        stval2 = xtval2;
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
  set_mepcc(newXepcc);
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
  let epcc : Capability = match p {
                            Machine    => mepcc,
                            Supervisor => sepcc,
                            User       => internal_error(__FILE__, __LINE__, "N extension not supported"),
                          };

  set_next_pcc(unsealCap(epcc));
  /* Similar to prepare_trap_vector above we need to return the absolute address
    destined for PC, rather than the offset (architecutral PC) */
  epcc.address
}

// TODO: This is duplicated in `riscv_sys_exceptions.sail` which is unfortunate.

mapping clause csr_name_map = 0x105  <-> "stvec"
mapping clause csr_name_map = 0x141  <-> "sepc"
mapping clause csr_name_map = 0x305  <-> "mtvec"
mapping clause csr_name_map = 0x341  <-> "mepc"

function clause is_CSR_defined(0x105) = extensionEnabled(Ext_S) // stvec
function clause is_CSR_defined(0x141) = extensionEnabled(Ext_S) // sepc
function clause is_CSR_defined(0x305) = true // mtvec
function clause is_CSR_defined(0x341) = true // mepc

function clause read_CSR(0x105, _) = get_stvec()
function clause read_CSR(0x141, _) = get_sepc()
function clause read_CSR(0x305, _) = get_mtvec()
function clause read_CSR(0x341, _) = get_mepc()

function clause write_CSR(0x105, value) = { set_stvec(value); get_stvec() }
function clause write_CSR(0x141, value) = { set_sepc(value); get_sepc() }
function clause write_CSR(0x305, value) = { set_mtvec(value); get_mtvec() }
function clause write_CSR(0x341, value) = { set_mepc(value); get_mepc() }
