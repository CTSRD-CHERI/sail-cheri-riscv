/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* CHERI uses a boolean tag as metadata in memory. */

type mem_meta = bool

let default_meta : mem_meta = false

/* address LSB truncation/extension */
type tagaddrbits = bits(xlen - log2_cap_size)
function addr_to_tag_addr(addr : xlenbits) -> tagaddrbits = truncateLSB(addr, xlen - log2_cap_size)
function tag_addr_to_addr(tag_addr : tagaddrbits) -> xlenbits = tag_addr @ zeros(log2_cap_size)

// This looks up the PMA based on the address.
// TODO: Since we have already looked up the PMA in `phys_access_check()` it
// would make much more sense just to pass it down to here, but that is a
// more invasive change.
val is_taggable : (xlenbits, mem_access_width) -> bool

/* FIXME: we should have a maximum cap_size constraint for 'n.
 * This would check that the assumption below of a max span of two regions is valid.
 */
function __WriteRAM_Meta(addr : xlenbits, width : mem_access_width, tag : mem_meta) -> unit = {
  // Clear tag if writing to untaggable memory.
  let tag = tag & is_taggable(addr, width);

  let tag_addr = addr_to_tag_addr(addr);
  if get_config_print_mem() then
    print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ (if tag then "1" else "0"));
  MEMw_tag(zero_extend(tag_addr), tag);
  /* If the write crosses a cap_size alignment boundary then we need
   * to write the tag for the subsequent region.  Writes greater than
   * cap_size that might span more than two regions are not supported.
   */
  let tag_addr2 = addr_to_tag_addr(addr + width - 1);
  if tag_addr != tag_addr2 then {
    if get_config_print_mem() then
      print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr2)) ^ "] <- " ^ (if tag then "1" else "0"));
    MEMw_tag(zero_extend(tag_addr2), tag);
  }
}

/* FIXME: we should have a maximum cap_size constraint for 'n. */
function __ReadRAM_Meta(addr : xlenbits, width : mem_access_width) -> mem_meta = {
  let tag_addr = addr_to_tag_addr(addr);
  let tag = MEMr_tag(zero_extend(tag_addr));
  if get_config_print_mem() then
    print_mem("tag[R," ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] -> " ^ (if tag then "1" else "0"));

  // Read false if reading from untaggable memory. We could potentially
  // get away without this since we never allow writing tags to untaggable
  // memory, and tags are reset to 0 and the taggable PMA is fixed.
  tag & is_taggable(addr, width)
}
