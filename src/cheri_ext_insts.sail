/* Instructions with opcode and field combinations that are not defined in the standard cheri spec
 * but in CHERI are defined here.
 */

function clause ext_execute (LOADRES(aq, rl, rs1, width, rd)) = {
  handle_illegal();
  false
}

function clause ext_execute (STORECON(aq, rl, rs2, rs1, width, rd)) = {
  handle_illegal();
  false
}
