function enter_debug_mode_with_next_pc(cause: DebugModeCause, next_pc: xlenbits) -> unit = {
  // save PCC in DPCC
  set_dpcc(PCC);
  // Force PCC to infinite cap with the mode set from dinfc
  PCC = setCapMode(infinite_cap, getCapMode(dinfc));
  nextPCC = PCC;
  // save DCC in DDDC
  set_dddc(ddc);
  // ddc <- almighty cap with ddc address
  ddc = { infinite_cap with address = ddc.address };

  enter_debug_mode_with_next_pc_default(cause, next_pc);
}

function enter_debug_mode(cause: DebugModeCause) -> unit =
  enter_debug_mode_default(cause)

function leave_debug_mode() -> unit = {
  // restore PCC
  nextPCC = unsealCap(dpcc);
  // restore DDC
  ddc = dddc;

  leave_debug_mode_default();
}

function dispatchDebugEntry() -> option((Retired, bool)) =
  dispatchDebugEntry_default()
