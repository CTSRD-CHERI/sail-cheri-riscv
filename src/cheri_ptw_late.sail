/*
 * Additional aspects of CHERI PTW logic that can refer back to the RISCV PTW
 */

/*
 * Dispatch to either translateAddr or translateAddr_priv if overriding privilege
 */
val translateAddr_optpriv : (OptPrivilege, xlenbits, AccessType(ext_access_type)) -> TR_Result(xlenbits, ExceptionType) effect {escape, rmem, rmemt, rreg, wmv, wmvt, wreg}
function translateAddr_optpriv(optpriv, vaddr, ac) =
  match optpriv {
    PrivDefault() => translateAddr(vaddr, ac),
    PrivOverride(p) => translateAddr_priv(vaddr, ac, p)
  }
