

function ext_post_decode_hook(x) : ast -> ast = {
  if (PCC.flag_cap_mode) then match(x) {
    UTYPE(imm, cd, RISCV_AUIPC) => AUIPCC(imm, cd),
    RISCV_JAL(imm, cd) => CJAL(imm, cd),
    RISCV_JALR(imm, cs1, cd) => CJALR(imm, cs1, cd),
    OTHERS => OTHERS
  } else
    x
}
