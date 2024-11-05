bitfield MEnvcfg : bits(64) = {
  // Supervisor TimeCmp Extension
  STCE   : 63,
  // Page Based Memory Types Extension
  PBMTE  : 62,
  // Reserved WPRI bits.
  wpri_2 : 61 .. 29,
  // CHERI Register Enable
  // Controls whether less privileged levels can perform explicit accesses to
  // CHERI registers. Less priviledged levels can read and write CHERI
  // registers when CRE=1 and can't when CRE=0.
  CRE    : 28,
  // Reserved WPRI bits.
  wpri_1 : 27 .. 8,
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
  // registers when CRE=1 and can't when CRE=0.
  CRE    : 28,
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

// Zcherihybrid adds a CRE bit to mseccfg
bitfield Seccfg : bits(64) = {
  // Enable access to SEED in S-mode
  SSEED  : 9,
  // Enable access to SEED in U-mode
  USEED  : 8,
  // Reserved WPRI bits
  wpri_1 : 7 .. 4,
  // CHERI Register Enable
  // Whether CHERI registers are enabled for M mode.
  CRE : 3,
  // Reserved WPRI bits
  wpri_0 : 2 .. 0,
}
