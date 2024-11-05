// Which instructions are illegal in debug mode?
function illegalInDebugMode(ast : ast) -> bool = match ast {
  RISCV_JAL(_, _) => debugIllegalCtrlTransferInstr(),
  RISCV_JALR(_, _, _) => debugIllegalCtrlTransferInstr(),
  BTYPE(_, _, _, _) => debugIllegalCtrlTransferInstr(),
  ECALL() => debugIllegalCtrlTransferInstr(),
  MRET() => debugIllegalCtrlTransferInstr(),
  SRET() => debugIllegalCtrlTransferInstr(),
  UTYPE(_, _, RISCV_AUIPC) => debugIllegalCtrlTransferInstr(),
  C_BNEZ(_, _) => debugIllegalCtrlTransferInstr(),
  C_JAL(_) => debugIllegalCtrlTransferInstr(),
  C_J(_) => debugIllegalCtrlTransferInstr(),
  C_BEQZ(_,_) => debugIllegalCtrlTransferInstr(),
  C_JR(_) => debugIllegalCtrlTransferInstr(),
  C_JALR(_) => debugIllegalCtrlTransferInstr(),
  // CHERI
  C_JALR_capmode(_) => debugIllegalCtrlTransferInstr(),
  C_JAL_capmode(_) => debugIllegalCtrlTransferInstr(),
  C_JR_capmode(_) => debugIllegalCtrlTransferInstr(),
  JALR_capmode(_, _, _) => debugIllegalCtrlTransferInstr(),
  JAL_capmode(_, _) => debugIllegalCtrlTransferInstr(),
  AUIPC_capmode(_) => debugIllegalCtrlTransferInstr(),

  _ => false,
}

// Execute an instruction, as long as it isn't one that is illegal in debug mode.
function execute_instruction(ast : ast) -> Retired = {
    if debug_mode_active & illegalInDebugMode(ast) then {
        handle_illegal();
        RETIRE_FAIL
    } else execute(ast)
}
