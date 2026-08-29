enum CSRLen = {
  // Standard RISC-V CSR
  Standard,
  // YLEN CSR
  Ylen,
}

function csr_type(csr : csreg) -> CSRLen = match csr {
  0x7b1 => Ylen, // dpc
  0x7b2 => Ylen, // dscratch0
  0x7b3 => Ylen, // dscratch1

  0x305 => Ylen, // mtvec
  0x340 => Ylen, // mscratch
  0x341 => Ylen, // mepc

  0x105 => Ylen, // stvec
  0x140 => Ylen, // sscratch
  0x141 => Ylen, // sepc

  0x780 => Ylen, // mtid
  0x580 => Ylen, // stid
  0x480 => Ylen, // utid

  0x7bc => Ylen, // dddc
  0x7bd => Ylen, // drootc

  0x416 => Ylen, // ddc

  _ => Standard,
}

// Return true if this is a YLEN-width CSR.
function is_ylen_csr(csr : csreg) -> bool = csr_type(csr) == Ylen

// Write a capability CSR (is_ylen_csr(csr) is true) with a Capability.
// It may undergo invalid address conversion.
function write_ylen_csr(csr : csreg, value : Capability) -> unit = {
  let stripTag = boundsMalformed(value) | permsMalformed(value) | not(capReservedValid(value));
  let value = { value with tag = value.tag & not(stripTag) };
  let res : Capability = match csr {
    // 0x7b1 => {set_dpcc(value); dpcc},
    // 0x7b2 => {set_dscratch0c(value); dscratch0c},
    // 0x7b3 => {set_dscratch1c(value); dscratch1c},
    // 0x7bc => {set_dddc(value); dddc},
    // 0x7bd => {set_drootc(value); drootc},

    0x305 => {set_mtvec_y(value); mtvec_y},
    0x340 => {set_mscratch_y(value); mscratch_y},
    0x341 => {set_mepc_y(value); mepc_y},

    0x105 => {set_stvec_y(value); stvec_y},
    0x140 => {set_sscratch_y(value); sscratch_y},
    0x141 => {set_sepc_y(value); sepc_y},

    0x416 => {set_ddc_y(value); ddc_y},

    0x780 => {set_mtid_y(value); mtid_y},
    0x580 => {set_stid_y(value); stid_y},
    0x480 => {set_utid_y(value); utid_y},

    _ => internal_error(__FILE__, __LINE__, "write_ylen_csr for XLEN CSR; this should not be possible"),
  };
  if   get_config_print_reg()
  then print_reg("CSR " ^ to_str(csr) ^ " <- " ^ capToString(res) ^ " (input: " ^ capToString(value) ^ ")")
}

// Write a capability CSR (is_ylen_csr(csr) is true) with xlenbits.
// It may undergo invalid address conversion, and the tag may be cleared.
function write_ylen_csr_with_xlen(csr : csreg, value : xlenbits) -> unit = {
  let res : Capability = match csr {
    // 0x7b1 => {let _ = set_dpc(value); dpcc},
    // 0x7b2 => {let _ = set_dscratch0(value); dscratch0c},
    // 0x7b3 => {let _ = set_dscratch1(value); dscratch1c},
    // 0x7bc => {let _ = set_dddc_xlen(value); dddc},
    // 0x7bd => {let _ = set_drootc_xlen(value); drootc},

    0x305 => {set_mtvec(value); mtvec_y},
    0x340 => {set_mscratch(value); mscratch_y},
    0x341 => {set_mepc(value); mepc_y},

    0x105 => {set_stvec(value); stvec_y},
    0x140 => {set_sscratch(value); sscratch_y},
    0x141 => {set_sepc(value); sepc_y},

    0x416 => {set_ddc_xlen(value); ddc_y},

    0x780 => {set_mtid(value); mtid_y},
    0x580 => {set_stid(value); stid_y},
    0x480 => {set_utid(value); utid_y},

    _ => internal_error(__FILE__, __LINE__, "write_ylen_csr_with_xlen for XLEN CSR; this should not be possible"),
  };
  if   get_config_print_reg()
  then print_reg("CSR " ^ to_str(csr) ^ " <- " ^ capToString(res) ^ " (input addr: " ^ BitStr(value) ^ ")")
}

// Read a capability CSR (is_ylen_csr(csr) is true) returning the entire capability.
// The write_val is only required for xscratchcsw[l]c and xtvtscaddrc CLIC CSRs
function read_ylen_csr(csr : csreg, write_val : Capability) -> Capability = match csr {
  // 0x7b1 => dpcc,
  // 0x7b2 => dscratch0c,
  // 0x7b3 => dscratch1c,
  // 0x7bc => dddc,
  // 0x7bd => get_drootc(),

  0x305 => mtvec_y,
  0x340 => mscratch_y,
  0x341 => mepc_y, // Note: this would require legalisation for implementations with writable misa.C.

  0x105 => stvec_y,
  0x140 => sscratch_y,
  0x141 => sepc_y,

  0x416 => ddc_y,

  0x780 => mtid_y,
  0x580 => stid_y,
  0x480 => utid_y,

  _ => internal_error(__FILE__, __LINE__, "read_ylen_csr for XLEN CSR; this should not be possible"),
}

// Handle CSR ops for CHERI. This special cases YLEN-width CSRs and delegates
// all other CSRs to the default non-CHERI handler.
function handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead) = {
  if is_ylen_csr(csr) then {
    // The only way to write metadata is with `csrrw`.
    // For extended CSRs, it also has to be in CapPtrMode mode.
    // Note `op == CSRRW` means `csrrw` or` csrrwi` which is why we also check `not(is_imm)`.
    let ylen_write = (effective_cheri_mode() == CapPtrMode) & op == CSRRW & not(is_imm);
    let write_val = if is_imm then {null_cap with address = zero_extend(regidx_bits(rs1))}
      else if ylen_write then Y(rs1)
      else {null_cap with address = X(rs1)};
    // Reads of YLEN registers are always YLEN.
    let csr_val = if isRead then read_ylen_csr(csr, write_val) else zero_reg;
    if isWrite then {
      if ylen_write then {
        write_ylen_csr(csr, write_val);
      } else {
        let new_val : xlenbits = match op {
          CSRRW => write_val.address,
          CSRRS => csr_val.address | write_val.address,
          CSRRC => csr_val.address & ~(write_val.address)
        };
        write_ylen_csr_with_xlen(csr, new_val);
      };
    };
    if effective_cheri_mode() == CapPtrMode then {
      Y(rd) = csr_val;
    } else {
      X(rd) = csr_val.address;
    };
    RETIRE_SUCCESS
  } else default_handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead)
}
