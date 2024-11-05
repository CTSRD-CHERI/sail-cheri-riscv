enum CSRLen = {
  // Standard RISC-V CSR
  Standard,
  // XLEN CSR extended to CLEN
  ClenExtended,
  // New CLEN CSR
  ClenNew,
}

function csr_type(csr : csreg) -> CSRLen = match csr {
  0x7b1 => ClenExtended, // dpcc
  0x7b2 => ClenExtended, // dscratch0c
  0x7b3 => ClenExtended, // dscratch1c

  0x305 => ClenExtended, // mtvecc
  0x340 => ClenExtended, // mscratchc
  0x341 => ClenExtended, // mepcc

  0x105 => ClenExtended, // stvecc
  0x140 => ClenExtended, // sscratchc
  0x141 => ClenExtended, // sepcc

  0x780 => ClenExtended, // mtidc
  0x580 => ClenExtended, // stidc
  0x480 => ClenExtended, // utidc

  0x7bc => ClenNew, // dddc
  0x7bd => ClenNew, // dinfc

  0x416 => ClenNew, // ddc

  0x74c => ClenNew, // mtdc
  0x163 => ClenNew, // stdc

  _ => Standard,
}

// Return true if this is a CLEN-width CSR.
function is_clen_csr(csr : csreg) -> bool = csr_type(csr) == ClenExtended | csr_type(csr) == ClenNew

// Write a capability CSR (is_clen_csr(csr) is true) with a Capability.
// It may undergo invalid address conversion.
function write_clen_csr(csr : csreg, value : Capability) -> unit = {
  let stripTag = boundsMalformed(value) | permsMalformed(value) | not(capReservedValid(value));
  let value = { value with tag = value.tag & not(stripTag) };
  let res : Capability = match csr {
    0x7b1 => {set_dpcc(value); dpcc},
    0x7b2 => {set_dscratch0c(value); dscratch0c},
    0x7b3 => {set_dscratch1c(value); dscratch1c},
    0x7bc => {set_dddc(value); dddc},
    0x7bd => {set_dinfc(value); dinfc},

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

    _ => internal_error(__FILE__, __LINE__, "write_clen_csr for XLEN CSR; this should not be possible"),
  };
  if   get_config_print_reg()
  then print_reg("CSR " ^ to_str(csr) ^ " <- " ^ capToString(res) ^ " (input: " ^ capToString(value) ^ ")")
}

// Write a capability CSR (is_clen_csr(csr) is true) with xlenbits.
// It may undergo invalid address conversion, and the tag may be cleared.
function write_clen_csr_with_xlen(csr : csreg, value : xlenbits) -> unit = {
  let res : Capability = match csr {
    0x7b1 => {let _ = set_dpc(value); dpcc},
    0x7b2 => {let _ = set_dscratch0(value); dscratch0c},
    0x7b3 => {let _ = set_dscratch1(value); dscratch1c},
    0x7bc => {let _ = set_dddc_xlen(value); dddc},
    0x7bd => {let _ = set_dinfc_xlen(value); dinfc},

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

    _ => internal_error(__FILE__, __LINE__, "write_clen_csr_with_xlen for XLEN CSR; this should not be possible"),
  };
  if   get_config_print_reg()
  then print_reg("CSR " ^ to_str(csr) ^ " <- " ^ capToString(res) ^ " (input addr: " ^ BitStr(value) ^ ")")
}

// Read a capability CSR (is_clen_csr(csr) is true) returning the entire capability.
function read_clen_csr(csr : csreg) -> Capability = match csr {
  0x7b1 => dpcc,
  0x7b2 => dscratch0c,
  0x7b3 => dscratch1c,
  0x7bc => dddc,
  0x7bd => get_dinfc(),

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

  _ => internal_error(__FILE__, __LINE__, "read_clen_csr for XLEN CSR; this should not be possible"),
}

// Handle CSR ops for CHERI. This special cases CLEN-width CSRs and delegates
// all other CSRs to the default non-CHERI handler.
function handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead) =
  if is_clen_csr(csr) then {
    // Reads of CLEN registers are always CLEN.
    let csr_val = if isRead then read_clen_csr(csr) else zero_reg;
    if isWrite then {
      // The only way to write metadata is with `csrrw`.
      // For extended CSRs, it also has to be in CapPtrMode mode.
      // Note `op == CSRRW` means `csrrw` or` csrrwi` which is why why also
      // check `not(is_imm)`.
      if (effective_cheri_mode() == CapPtrMode | csr_type(csr) == ClenNew) & op == CSRRW & not(is_imm) then {
        write_clen_csr(csr, C(rs1));
      } else {
        let rs1_val : xlenbits = if is_imm then zero_extend(rs1) else X(rs1);
        let new_val : xlenbits = match op {
          CSRRW => rs1_val,
          CSRRS => csr_val.address | rs1_val,
          CSRRC => csr_val.address & ~(rs1_val)
        };
        write_clen_csr_with_xlen(csr, new_val);
      };
    };
    if effective_cheri_mode() == CapPtrMode then {
      C(rd) = csr_val;
    } else {
      X(rd) = csr_val.address;
    };
    RETIRE_SUCCESS
  } else default_handle_csr_op(csr, rs1, rd, is_imm, op, isWrite, isRead)
