/* CHERI uses a boolean tag as metadata in memory. */

type mem_meta = bool

let default_meta : mem_meta = false

/* address alignment */
/* FIXME: should derive this from cap_size */
function tag_align_addr(addr : xlenbits) -> xlenbits = [addr with 3..0 = 0x0]

/* FIXME: we should have a maximum cap_size constraint for 'n.
 * This would check that the assumption below of a max span of two regions is valid.
 */
val __WriteRAM_Meta : forall 'n. (xlenbits, atom('n), mem_meta) -> unit effect {wmvt}
function __WriteRAM_Meta(addr, width, tag) = {
  let tag_addr = tag_align_addr(addr);
  print_mem("tag[" ^ BitStr(tag_addr) ^ "] <- " ^ (if tag then "1" else "0"));
  MEMw_tag(tag_addr, tag);
  /* If the write crosses a cap_size alignment boundary then we need
   * to write the tag for the subsequent region.  Writes greater than
   * cap_size that might span more than two regions are not supported.
   */
  let tag_addr2 = tag_align_addr(addr + width - 1);
  if tag_addr != tag_addr2 then {
    print_mem("tag[" ^ BitStr(tag_addr2) ^ "] <- " ^ (if tag then "1" else "0"));
    MEMw_tag(tag_addr2, tag);
  }
}

/* FIXME: we should have a maximum cap_size constraint for 'n. */
val __ReadRAM_Meta  : forall 'n. (xlenbits, atom('n)) -> mem_meta effect {rmemt}
function __ReadRAM_Meta(addr, width) = {
  let tag_addr = tag_align_addr(addr);
  MEMr_tag(addr)
}
