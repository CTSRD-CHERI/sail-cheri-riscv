bitfield MEnvcfg : bits(64) = {
  // Supervisor TimeCmp Extension
  STCE   : 63,
  // Page Based Memory Types Extension
  PBMTE  : 62,
  // Reserved WPRI bits.
  wpri_2 : 61 .. 10,
  // CHERI Register Enable
  // Controls whether less privileged levels can perform explicit accesses to
  // CHERI registers. Less priviledged levels can read and write CHERI
  // registers when Y=1 and can't when Y=0.
  Y      : 9,
  // Reserved WPRI bits.
  wpri_1 : 8,
  // Cache Block Zero instruction Enable
  CBZE   : 7,
  // Cache Block Clean and Flush instruction Enable
  CBCFE  : 6,
  // Cache Block Invalidate instruction Enable
  CBIE   : 5 .. 4,
  // Reserved WPRI bits.
  wpri_0 : 3 .. 1,
  // Fence of I/O implies Memory
  FIOM   : 0,
}

bitfield SEnvcfg : xlenbits = {
  // CHERI Register Enable
  // Controls whether less privileged levels can perform explicit accesses to
  // CHERI registers. Less priviledged levels can read and write CHERI
  // registers when Y=1 and can't when Y=0.
  Y      : 9,
  // Cache Block Zero instruction Enable
  CBZE   : 7,
  // Cache Block Clean and Flush instruction Enable
  CBCFE  : 6,
  // Cache Block Invalidate instruction Enable
  CBIE   : 5 .. 4,
  // Reserved WPRI bits.
  wpri_0 : 3 .. 1,
  // Fence of I/O implies Memory
  FIOM   : 0,
}
