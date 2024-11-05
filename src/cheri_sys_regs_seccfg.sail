/* whether Zkr was enabled at boot */
val sys_enable_zkr = {c: "sys_enable_zkr", ocaml: "Platform.enable_zkr", _: "sys_enable_zkr"} : unit -> bool

function legalize_mseccfg(o : Seccfg, v : bits(64)) -> Seccfg = {
  let v = Mk_Seccfg(v);
  [
    o with
    SSEED = if sys_enable_zkr() then v[SSEED] else 0b0,
    USEED = if sys_enable_zkr() then v[USEED] else 0b0,
    CRE = v[CRE],
  ]
}
