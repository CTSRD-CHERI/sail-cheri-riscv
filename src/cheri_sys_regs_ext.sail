/* Veto disabling C if PCC.base is not 4-byte aligned
   (assuming it is already 2-byte aligned) */
function ext_veto_disable_C () = getCapBaseBits(PCC)[1] == bitone

/* FIXME: This should be changed to reflect what's needed for sentries. */
function legalize_xepc(v : xlenbits) -> xlenbits =
  /* allow writing xepc[1] only if misa.C is enabled or could be enabled */
  if   (sys_enable_writable_misa() & sys_enable_rvc()) | misa.C() == 0b1
  then [v with 0 = bitzero]
  else v & EXTS(0b100)

function legalize_epcc (v : Capability) -> Capability = {
  setCapOffsetOrNull(v, legalize_xepc(getCapOffsetBits(v)))
}
