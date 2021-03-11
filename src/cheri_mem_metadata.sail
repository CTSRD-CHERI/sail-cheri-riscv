/* CHERI uses a boolean tag and version as metadata in memory. 
   Options so that we can independently write tag and version. */
union mem_meta = {
  Meta_Tag : bool,
  Meta_Ver : CapVersionBits,
  Meta_TagVer   : (bool, CapVersionBits)
}

let default_meta : mem_meta = Meta_Tag(false)
let version_granule_size = cap_size
type version_granules_per_cache_line : Int = caps_per_cache_line
let version_granules_per_cache_line = sizeof(version_granules_per_cache_line)

/* address LSB truncation/extension */
type tagaddrbits = bits(xlen - log2_cap_size)
function addr_to_tag_addr(addr : xlenbits) -> tagaddrbits = truncateLSB(addr, sizeof(xlen) - log2_cap_size)
function tag_addr_to_addr(tag_addr : tagaddrbits) -> xlenbits = tag_addr @ zeros(log2_cap_size)

function write_tag_with_log(tag_addr: tagaddrbits, t : bool) -> unit = {
  if get_config_print_mem() then
    print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ (if t then "1" else "0"));
  MEMw_tag(EXTZ(tag_addr), t);
}

function write_ver_with_log(tag_addr: tagaddrbits, v :CapVersionBits) -> unit = {
  if get_config_print_mem() then
    print_mem("ver[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ BitStr(v));
  MEMw_tag_byte(EXTZ(tag_addr), EXTZ(v));
}

/**
  * Writes tag and version to aligned granule.
  */
function write_ram_mtag_mver(tag_addr : tagaddrbits, meta : mem_meta) -> unit = {
  match(meta) {
    Meta_Tag(t)       => write_tag_with_log(tag_addr, t),
    Meta_TagVer(t, _) => write_tag_with_log(tag_addr, t),
    _ => ()
  };
  match (meta) {
    Meta_Ver(v)       => write_ver_with_log(tag_addr, v),
    Meta_TagVer(_, v) => write_ver_with_log(tag_addr, v),
    _ => ()
  }
}

/* FIXME: we should have a maximum cap_size constraint for 'n.
 * This would check that the assumption below of a max span of two regions is valid.
 */
val __WriteRAM_Meta : forall 'n. (xlenbits, atom('n), mem_meta) -> unit effect {wmvt}
function __WriteRAM_Meta(addr, width, meta) = {
  let tag_addr = addr_to_tag_addr(addr);
  write_ram_mtag_mver(tag_addr, meta);
  /* If the write crosses a cap_size alignment boundary then we need
   * to write the tag for the subsequent region.  Writes greater than
   * cap_size that might span more than two regions are not supported.
   */
  let tag_addr2 = addr_to_tag_addr(addr + width - 1);
  if tag_addr != tag_addr2 then write_ram_mtag_mver(tag_addr2, meta);
}
/* FIXME: we should have a maximum cap_size constraint for 'n. */
val __ReadRAM_Meta  : forall 'n. (xlenbits, atom('n)) -> mem_meta effect {rmemt}
function __ReadRAM_Meta(addr, width) = {
  let tag_addr = addr_to_tag_addr(addr);
  let tag_addr64 : bits(64) = EXTZ(tag_addr);
  let tag : bool = MEMr_tag(tag_addr64);
  let ver : CapVersionBits = truncate(MEMr_tag_byte(tag_addr64), cap_version_width);
  if get_config_print_mem() then {
    let tag_addr_str = BitStr(tag_addr_to_addr(tag_addr));
    print_mem("tag[R," ^ tag_addr_str ^ "] -> " ^ (if tag then "1" else "0"));
    print_mem("ver[R," ^ tag_addr_str ^ "] -> " ^ BitStr(ver));
  };
  Meta_TagVer(tag, ver)
}
