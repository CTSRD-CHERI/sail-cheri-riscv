/* CHERI interface to physical memory.  We use the metadata facility for tags. */

val mem_read_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(Capability) effect {rmem, rmemt, rreg, escape}
function mem_read_cap (addr, aq, rl, res) = {
  let result : MemoryOpResult(CapBits) =
    if   ~(is_aligned_addr(addr, cap_size))
    then MemException(E_Load_Addr_Align)
    else match (aq, rl, res) {
           (false, true,  false) => throw(Error_not_implemented("load.rl")),
           (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
           (_, _, _)             => checked_mem_read(Read, addr, cap_size, aq, rl, res)
    };

  /* It's more idiomatic here to use __ReadRAM_Meta, but we are doing
   * two address alignment checks, one above, and one in
   * __ReadRAM_Meta.  There is a risk of them becoming inconsistent.  The
   * alternative is to directly use MEMr_tag, which would be less
   * idiomatic.
   */
  //let tag = MEMr_tag(addr);
  let tag = __ReadRAM_Meta(addr, cap_size);
  match result {
    MemValue(v)     => MemValue(memBitsToCapability(tag, v)),
    MemException(e) => MemException(e) : MemoryOpResult(Capability)
  }
}

val mem_write_ea_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(unit) effect {eamem}
function mem_write_ea_cap(addr, aq, rl, con) = {
  if   ~(is_aligned_addr(addr, cap_size))
  then MemException(E_SAMO_Addr_Align)
  else MemValue(__write_mem_ea(Write_plain, sizeof(xlen), addr, cap_size)) // FIXME: is Write_plain correct?
}

val mem_write_cap : (xlenbits, Capability, bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape, wmvt}
function mem_write_cap (addr, cap, aq, rl, con) = {
  let cap_bits = capToMemBits(cap);
  mem_write_value_meta(addr, cap_size, cap_bits, cap.tag, aq, rl, con)
}
