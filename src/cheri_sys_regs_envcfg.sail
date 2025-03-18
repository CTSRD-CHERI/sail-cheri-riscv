// TODO: factor out code common to legalize_menvcfg and legalize_senvcfg.

/* Whether FIOM bit of menvcfg/senvcfg is enabled. It must be enabled if
   supervisor mode is implemented and non-bare addressing modes are supported. */
val sys_enable_writable_fiom = pure "sys_enable_writable_fiom" : unit -> bool

// Is PBMT supported?
val sys_enable_pbmt = pure "sys_enable_pbmt" : unit -> bool

function legalize_menvcfg(o : MEnvcfg, m : Seccfg, v : bits(64)) -> MEnvcfg = {
  let v = Mk_MEnvcfg(v);
  [o with
    FIOM = if sys_enable_writable_fiom() then v[FIOM] else 0b0,
    STCE = if extensionEnabled(Ext_Sstc) then v[STCE] else 0b0,
    CBZE = if extensionEnabled(Ext_Zicboz) then v[CBZE] else 0b0,
    CBCFE = if extensionEnabled(Ext_Zicbom) then v[CBCFE] else 0b0,
    CBIE = if extensionEnabled(Ext_Zicbom) then (if v[CBIE] != 0b10 then v[CBIE] else 0b00) else 0b00,
    PBMTE = if sys_enable_pbmt() then v[PBMTE] else 0b0,
    CRE = v[CRE],
    // Other extensions are not implemented yet so all other fields are read only zero.
  ]
}

function legalize_senvcfg(o : SEnvcfg, m : MEnvcfg, v : xlenbits) -> SEnvcfg = {
  let v = Mk_SEnvcfg(v);
  [o with
    FIOM = if sys_enable_writable_fiom() then v[FIOM] else 0b0,
    CBZE = if extensionEnabled(Ext_Zicboz) then v[CBZE] else 0b0,
    CBCFE = if extensionEnabled(Ext_Zicbom) then v[CBCFE] else 0b0,
    CBIE = if extensionEnabled(Ext_Zicbom) then (if v[CBIE] != 0b10 then v[CBIE] else 0b00) else 0b00,
    CRE = v[CRE],
    // Other extensions are not implemented yet so all other fields are read only zero.
  ]
}
