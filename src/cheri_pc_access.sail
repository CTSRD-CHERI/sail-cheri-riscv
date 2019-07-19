/* accessors for default architectural addresses, for use from within instructions */

val get_arch_pc : unit -> xlenbits effect {rreg}
function get_arch_pc () =
  PC - getCapBaseBits(PCC)

/* FIXME: The asymmetry between get_next_pc and set_next_pc where one
 * returns the architectural PC but the other set the PCC-relative PC
 * is a bit weird. The way they are currently used it is correct but
 * we should either rename one of the functions or call set_next_pc
 * with the original target address instead of the munged one. - RNW.
 */

val get_next_pc : unit -> xlenbits effect {rreg}
function get_next_pc() =
  nextPC - getCapBaseBits(PCC)

val set_next_pc : xlenbits -> unit effect {wreg}
function set_next_pc(pc) =
  /* could check for internal errors here on invalid pc */
  nextPC = pc

val tick_pc : unit -> unit effect {rreg, wreg}
function tick_pc() = {
  PCC = nextPCC;
  PC = nextPC
}
