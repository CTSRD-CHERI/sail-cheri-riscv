

function ext_post_decode_hook(x) = {
  if (PCC.flag_cap_mode) then match(x) {
    LOAD(imm, rs1, rd, is_unsigned, size, aq, rl) => CAP_LOAD(imm, rs1, rd, is_unsigned, size, aq, rl),
    STORE(imm, rs2, rs1, width, aq, rl)           => CAP_STORE(imm, rs2, rs1, width, aq, rl),
    UTYPE(imm, rd, RISCV_AUIPC)                   => CAP_AUIPC(imm, rd),
    OTHERS => OTHERS
  } else
    x
}