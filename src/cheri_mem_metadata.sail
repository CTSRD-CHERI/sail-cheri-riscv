/* CHERI uses a boolean tag as metadata in memory. */

type mem_meta = bool

let default_meta : mem_meta = false

/* address LSB truncation/extension */
type tagaddrbits = bits(xlen - log2_cap_size)
function addr_to_tag_addr(addr : xlenbits) -> tagaddrbits = truncateLSB(addr, sizeof(xlen) - log2_cap_size)
function tag_addr_to_addr(tag_addr : tagaddrbits) -> xlenbits = tag_addr @ zeros(log2_cap_size)

/* FIXME: we should have a maximum cap_size constraint for 'n.
 * This would check that the assumption below of a max span of two regions is valid.
 */
val __WriteRAM_Meta : forall 'n. (xlenbits, atom('n), mem_meta) -> unit effect {wmvt}
function __WriteRAM_Meta(addr, width, tag) = {
  let tag_addr = addr_to_tag_addr(addr);
  if get_config_print_mem() then
    print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ (if tag then "1" else "0"));
  MEMw_tag(EXTZ(tag_addr), tag);
  /* If the write crosses a cap_size alignment boundary then we need
   * to write the tag for the subsequent region.  Writes greater than
   * cap_size that might span more than two regions are not supported.
   */
  let tag_addr2 = addr_to_tag_addr(addr + width - 1);
  if tag_addr != tag_addr2 then {
    if get_config_print_mem() then
      print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr2)) ^ "] <- " ^ (if tag then "1" else "0"));
    MEMw_tag(EXTZ(tag_addr2), tag);
  }
}

/* FIXME: we should have a maximum cap_size constraint for 'n. */
val __ReadRAM_Meta  : forall 'n. (xlenbits, atom('n)) -> mem_meta effect {rmemt}
function __ReadRAM_Meta(addr, width) = {
  let tag_addr = addr_to_tag_addr(addr);
  let tag = MEMr_tag(EXTZ(tag_addr));
  if get_config_print_mem() then
    print_mem("tag[R," ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] -> " ^ (if tag then "1" else "0"));
  tag
}
