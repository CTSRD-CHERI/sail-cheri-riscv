

function ext_post_decode_hook(x) = {
  if (PCC.flag_cap_mode) then match(x) {
    LOAD(imm, rs1, rd, is_unsigned, size, aq, rl) => CAP_LOAD(imm, rs1, rd, is_unsigned, size, aq, rl),
    OTHERS => OTHERS
  } else
    x
}