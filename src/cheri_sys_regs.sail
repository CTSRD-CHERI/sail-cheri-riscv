/* CHERI system CSRs */

/* Capability control csr */

bitfield ccsr : bits(64) = {
  cap_idx : 13 .. 8,
  cause   :  7 .. 3, /* cap cause */
  m       :  2,      /* mode */
  d       :  1,      /* dirty  */
  e       :  0       /* enable */
}

register mccsr : ccsr
register sccsr : ccsr
register uccsr : ccsr

/* Other architectural registers */

register PCC       : Capability
register nextPCC   : Capability
register DDC       : Capability

register UTCC      : Capability
register UScratchC : Capability
register UEPCC     : Capability
register STCC      : Capability
register SScratchC : Capability
register SEPCC     : Capability
register MTCC      : Capability
register MScratchC : Capability
register MEPCC     : Capability

/* Cheri PCC helpers */

function min_instruction_bytes () -> uint64 = {
  if   (~ (sys_enable_writable_misa ())) & (~ (sys_enable_rvc ()))
  then 4  /* RVC is hardwired to be disabled */
  else 2  /* RVC is active or it could become active */
}

/* Checking whether the Xcheri extension is enabled */

function haveXcheri () -> bool =
  /* This is a necessary but not sufficient condition, but should do for now. */
  misa.X() == true
