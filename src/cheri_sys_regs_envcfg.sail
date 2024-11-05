// TODO: factor out code common to legalize_menvcfg and legalize_senvcfg.

/* Whether FIOM bit of menvcfg/senvcfg is enabled. It must be enabled if
   supervisor mode is implemented and non-bare addressing modes are supported. */
val sys_enable_writable_fiom = {c: "sys_enable_writable_fiom", ocaml: "Platform.enable_writable_fiom", _: "sys_enable_writable_fiom"} : unit -> bool

// Is PBMT supported?
val sys_enable_pbmt = {c: "sys_enable_pbmt", ocaml: "Platform.enable_pbmt", _:"sys_enable_pbmt"} : unit -> bool

// TODO: Reorganise the files so this goes in a more logical place.
// Is the Sstc stimecmp extension supported.
val sys_enable_sstc = pure "sys_enable_sstc" : unit -> bool
/* Supervisor timecmp */
enum clause extension = Ext_Sstc
function clause extensionEnabled(Ext_Sstc) = sys_enable_sstc()

function legalize_menvcfg(o : MEnvcfg, m : Seccfg, v : bits(64)) -> MEnvcfg = {
  let v = Mk_MEnvcfg(v);
  [o with
    FIOM = if sys_enable_writable_fiom() then v[FIOM] else 0b0,
    STCE = if extensionEnabled(Ext_Sstc) then v[STCE] else 0b0,
    CBZE = v[CBZE],
    CBCFE = v[CBCFE],
    CBIE = if v[CBIE]!= 0b10 then v[CBIE] else 0b00,
    PBMTE = if sys_enable_pbmt() then v[PBMTE] else 0b0,
    CRE = v[CRE],
    // Other extensions are not implemented yet so all other fields are read only zero.
  ]
}

function legalize_senvcfg(o : SEnvcfg, m : MEnvcfg, v : xlenbits) -> SEnvcfg = {
  let v = Mk_SEnvcfg(v);
  [o with
    FIOM = if sys_enable_writable_fiom() then v[FIOM] else 0b0,
    CBZE = v[CBZE],
    CBCFE = v[CBCFE],
    CBIE = if v[CBIE]!= 0b10 then v[CBIE] else 0b00,
    CRE = v[CRE],
    // Other extensions are not implemented yet so all other fields are read only zero.
  ]
}
