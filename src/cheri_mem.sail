/* CHERI interface to physical memory.  We use the metadata facility for tags. */

val mem_read_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(Capability) effect {rmem, rmemt, rreg, escape}
function mem_read_cap (addr, aq, rl, res) = {
  let result : MemoryOpResult((CapBits, bool)) = mem_read_meta(Read(Data), addr, cap_size, aq, rl, res, true);
  match result {
    MemValue(v, tag) => MemValue(memBitsToCapability(tag, v)),
    MemException(e)  => MemException(e) : MemoryOpResult(Capability)
  }
}

val mem_write_ea_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(unit) effect {eamem}
function mem_write_ea_cap(addr, aq, rl, con) = {
  if   ~(is_aligned_addr(addr, cap_size))
  then MemException(E_SAMO_Addr_Align())
  else MemValue(__write_mem_ea(Write_plain, sizeof(xlen), addr, cap_size)) // FIXME: is Write_plain correct?
}

val mem_write_cap : (xlenbits, Capability, bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape, wmvt}
function mem_write_cap (addr, cap, aq, rl, con) = {
  let cap_bits = capToMemBits(cap);
  /* Assume that conversion to bits and back does not change the capability.
     TODO: State closed-form normalised-ness criterion that implies this,
     and prove it as an invariant of capabilities in the system. */
  assert(memBitsToCapability(cap.tag, cap_bits) == cap);
  mem_write_value_meta(addr, cap_size, cap_bits, Cap, cap.tag, aq, rl, con)
}
