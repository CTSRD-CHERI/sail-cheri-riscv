bitfield Mstatus : bits(64) = {
  SD   : xlen - 1,

  // UCRG only exists for RV64-CHERI
  // It is set explicitly only in the methods below
  UCRG : xlen - 3,

  //MDT  : 42,
  //MPELP: 41,

  //MPV  : 39,
  //GVA  : 38,

  MBE  : 37,
  SBE  : 36,

  SXL  : 35 .. 34,
  UXL  : 33 .. 32,

  //SDT  : 24,
  //SPELP: 23,
  TSR  : 22,
  TW   : 21,
  TVM  : 20,
  MXR  : 19,
  SUM  : 18,
  MPRV : 17,

  XS   : 16 .. 15,
  FS   : 14 .. 13,

  MPP  : 12 .. 11,
  VS   : 10 .. 9,
  SPP  : 8,

  MPIE : 7,
  SPIE : 5,

  MIE  : 3,
  SIE  : 1,
}

bitfield Sstatus : bits(64) = {
  SD   : xlen - 1,
  UCRG : xlen - 3,

  UXL   : 33 .. 32,
//  SDT   : 24,
//  SPELP : 23,
  MXR   : 19,
  SUM   : 18,
  XS    : 16 .. 15,
  FS    : 14 .. 13,
  VS    : 10 .. 9,
  SPP   : 8,
  SPIE  : 5,
  SIE   : 1,
}

function ext_legalize_mstatus(m : Mstatus, v : Mstatus) -> Mstatus = {
  if xlen == 64 then [m with UCRG = v[UCRG]] else m;
}

function ext_lower_mstatus(m : Mstatus, s : Sstatus) -> Sstatus = {
  if xlen == 64 then [s with UCRG = m[UCRG]] else s;
}

function ext_lift_sstatus(m : Mstatus, s : Sstatus) -> Mstatus = {
  if xlen == 64 then [m with UCRG = s[UCRG]] else m;
}
