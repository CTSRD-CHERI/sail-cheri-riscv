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
type tagaddrbits = bits(physaddrbits_len - log2_cap_size)
function addr_to_tag_addr(addr : physaddrbits) -> tagaddrbits = addr[physaddrbits_len - 1 .. log2_cap_size]
function tag_addr_to_addr(tag_addr : tagaddrbits) -> physaddrbits = tag_addr @ zeros(log2_cap_size)

// This looks up the PMA based on the address.
// TODO: Since we have already looked up the PMA in `phys_access_check()` it
// would make much more sense just to pass it down to here, but that is a
// more invasive change.
val is_taggable : (physaddr, mem_access_width) -> bool

/*
 * FIXME: These interfaces are a poor fit for how CHERI tags work, due to
 * having a single tag argument / return value for any arbitrary range. Trust
 * the caller to do the right thing and not expect the impossible, but also
 * add in some safety checks to avoid things going off the rails in a way that
 * violates CHERI's unforgeability.
 *
 * NB: Neither cap_size nor is_aligned_addr are available to use here, so we
 * have to do things the ugly way.
 */
function is_cap_sized_aligned_access(addr : physaddrbits, width : mem_access_width) -> bool =
  width == 2 ^ log2_cap_size & addr[log2_cap_size - 1 .. 0] == zeros(log2_cap_size)

function __WriteRAM_Meta(addr : physaddrbits, width : mem_access_width, tag : mem_meta) -> unit = {
  assert(not(tag) | is_cap_sized_aligned_access(addr, width),
         "can only set tag for capability sized-and-aligned writes");

  // Clear tag if writing to untaggable memory.
  let tag = tag & is_taggable(physaddr(addr), width);

  // Unaligned stores can cross capability boundaries, clobbering two different
  // tags, and CBO.ZERO is implemented as a single large write that clobbers
  // multiple, so handle arbitrary ranges. The assertion above will guarantee
  // that the only time the loop body is executed more than once is when the
  // tag is zero, i.e. it's not possible for this loop to plaster a set tag
  // across memory and forge capabilities.
  //
  // NB: This may wrap the address space, so we must subtract the tagaddrbits
  // values before converting to any other representation (whether a different
  // width bitvector or an integer type like unsigned).
  let tag_range_first = addr_to_tag_addr(addr);
  let tag_range_last = addr_to_tag_addr(addr + width - 1);
  foreach (i from 0 to unsigned(tag_range_last - tag_range_first)) {
    let tag_addr = tag_range_first + i;
    if get_config_print_mem() then
      print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ (if tag then "1" else "0"));
    MEMw_tag(zero_extend(tag_addr), tag);
  }
}

function __ReadRAM_Meta(addr : physaddrbits, width : mem_access_width) -> mem_meta = {
  let tag_addr = addr_to_tag_addr(addr);
  let tag = MEMr_tag(zero_extend(tag_addr));
  if get_config_print_mem() then
    print_mem("tag[R," ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] -> " ^ (if tag then "1" else "0"));

  // Read false if reading from untaggable memory. We could potentially
  // get away without this since we never allow writing tags to untaggable
  // memory, and tags are reset to 0 and the taggable PMA is fixed.
  //
  // Similarly, throw away the tag if not a capability sized-and-aligned read;
  // nothing should be using the tag if so, but best to make it impossible to
  // get wrong.
  tag & is_taggable(physaddr(addr), width) & is_cap_sized_aligned_access(addr, width)
}
