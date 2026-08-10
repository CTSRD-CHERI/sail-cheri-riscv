enum CSRLen = {
  // Standard RISC-V CSR
  Standard,
  // XLEN CSR extended to YLEN
  YlenExtended,
  // New YLEN CSR
  YlenNew,
}

function csr_type(csr : csreg) -> CSRLen = match csr {
  0x7b1 => YlenExtended, // dpcc
  0x7b2 => YlenExtended, // dscratch0c
  0x7b3 => YlenExtended, // dscratch1c

  0x305 => YlenExtended, // mtvecc
  0x340 => YlenExtended, // mscratchc
  0x341 => YlenExtended, // mepcc

  0x105 => YlenExtended, // stvecc
  0x140 => YlenExtended, // sscratchc
  0x141 => YlenExtended, // sepcc

  0x780 => YlenExtended, // mtidc
  0x580 => YlenExtended, // stidc
  0x480 => YlenExtended, // utidc

  0x7bc => YlenNew, // dddc
  0x7bd => YlenNew, // dinfc

  0x416 => YlenNew, // ddc

  0x74c => YlenNew, // mtdc
  0x163 => YlenNew, // stdc

  _ => Standard,
}

// Return true if this is a YLEN-width CSR.
function is_ylen_csr(csr : csreg) -> bool = csr_type(csr) == YlenExtended | csr_type(csr) == YlenNew

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
    // 0x7bd => {set_dinfc(value); dinfc},

    0x305 => {set_mtvecc(value); mtvecc},
    0x340 => {set_mscratchc(value); mscratchc},
    0x341 => {set_mepcc(value); mepcc},

    0x105 => {set_stvecc(value); stvecc},
    0x140 => {set_sscratchc(value); sscratchc},
    0x141 => {set_sepcc(value); sepcc},

    0x416 => {set_ddc(value); ddc},

    0x74c => {set_mtdc(value); mtdc},
    0x163 => {set_stdc(value); stdc},

    0x780 => {set_mtidc(value); mtidc},
    0x580 => {set_stidc(value); stidc},
    0x480 => {set_utidc(value); utidc},

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
    // 0x7bd => {let _ = set_dinfc_xlen(value); dinfc},

    0x305 => {set_mtvec(value); mtvecc},
    0x340 => {set_mscratch(value); mscratchc},
    0x341 => {set_mepc(value); mepcc},

    0x105 => {set_stvec(value); stvecc},
    0x140 => {set_sscratch(value); sscratchc},
    0x141 => {set_sepc(value); sepcc},

    0x416 => {set_ddc_xlen(value); ddc},

    0x74c => {set_mtdc_xlen(value); mtdc},
    0x163 => {set_stdc_xlen(value); stdc},

    0x780 => {set_mtid(value); mtidc},
    0x580 => {set_stid(value); stidc},
    0x480 => {set_utid(value); utidc},

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
  // 0x7bd => get_dinfc(),

  0x305 => mtvecc,
  0x340 => mscratchc,
  0x341 => mepcc, // Note: this would require legalisation for implementations with writable misa.C.

  0x105 => stvecc,
  0x140 => sscratchc,
  0x141 => sepcc,

  0x416 => ddc,

  0x74c => mtdc,
  0x163 => stdc,

  0x780 => mtidc,
  0x580 => stidc,
  0x480 => utidc,

  _ => internal_error(__FILE__, __LINE__, "read_ylen_csr for XLEN CSR; this should not be possible"),
}

// Handle CSR ops for CHERI. This special cases YLEN-width CSRs and delegates
// all other CSRs to the default non-CHERI handler.
function handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead) = {
  if is_ylen_csr(csr) then {
    // The only way to write metadata is with `csrrw`.
    // For extended CSRs, it also has to be in CapPtrMode mode.
    // Note `op == CSRRW` means `csrrw` or` csrrwi` which is why we also check `not(is_imm)`.
    let ylen_write = (effective_cheri_mode() == CapPtrMode | csr_type(csr) == YlenNew) & op == CSRRW & not(is_imm);
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
    if effective_cheri_mode() == CapPtrMode | csr_type(csr) == YlenNew then {
      Y(rd) = csr_val;
    } else {
      X(rd) = csr_val.address;
    };
    RETIRE_SUCCESS
  } else default_handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead)
}
