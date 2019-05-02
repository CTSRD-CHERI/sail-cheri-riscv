

function ext_post_decode_hook(x) : ast -> ast = {
  if (PCC.flag_cap_mode) then match(x) {
    UTYPE(imm, rd, RISCV_AUIPC) => CAP_AUIPC(imm, rd),
    OTHERS => OTHERS
  } else
    x
}