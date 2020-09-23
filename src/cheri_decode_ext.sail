

function ext_post_decode_hook(x) : ast -> ast = {
  if (PCC.flag_cap_mode) then match(x) {
    UTYPE(imm, cd, RISCV_AUIPC) => AUIPCC(imm, cd),
    OTHERS => OTHERS
  } else
    x
}
