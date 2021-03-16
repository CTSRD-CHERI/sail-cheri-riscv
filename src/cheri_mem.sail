/* CHERI interface to physical memory.  We use the metadata facility for tags. */

val mem_read_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(Capability) effect {rmem, rmemt, rreg, escape}
function mem_read_cap (addr, aq, rl, res) = {
  let result : MemoryOpResult((CapBits, mem_meta)) = mem_read_meta(Read(Data), addr, cap_size, aq, rl, res, true);
  match result {
    MemValue(v, Meta_TagVer(tag, _)) => MemValue(memBitsToCapability(tag, v)),
    MemException(e)  => MemException(e) : MemoryOpResult(Capability),
    _ => internal_error("mem_read_meta didn't return cap+tag or exception")
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
  mem_write_value_meta(addr, cap_size, cap_bits, Cap, Meta_Tag(cap.tag), aq, rl, con)
}

val mem_read_version : xlenbits -> MemoryOpResult(CapVersionBits)
function mem_read_version(addr) = {
  if   ~(is_aligned_addr(addr, version_granule_size))
  then MemException(E_SAMO_Addr_Align())
  else {
    let result : MemoryOpResult((CapBits, mem_meta)) = mem_read_meta(Read(Version), addr, version_granule_size, false, false, false, true);
    match result {
      MemValue(_, Meta_TagVer(_, v)) => MemValue(v),
      MemException(e)  => MemException(e) : MemoryOpResult(CapVersionBits),
      _ => internal_error("mem_read_meta didn't to return version or exception")
    }
  }
}

val mem_write_ea_version : xlenbits -> MemoryOpResult(unit)
function mem_write_ea_version(addr) = {
  if   ~(is_aligned_addr(addr, version_granule_size))
  then MemException(E_SAMO_Addr_Align())
  else MemValue(__write_mem_ea(Write_plain, sizeof(xlen), addr, version_granule_size)) // FIXME: is Write_plain correct?
}

val mem_write_version : (xlenbits, CapVersionBits) -> MemoryOpResult(unit)
function mem_write_version(addr, v) = {
  if ~(is_aligned_addr(addr, version_granule_size))
  then MemException(E_SAMO_Addr_Align())
  else {
    /* XXX hack we don't have API to write only meta 
       so do read-modify write of cap + metadata */
    let result : MemoryOpResult((CapBits, mem_meta)) = 
      mem_read_meta(Read(Version), addr, version_granule_size, false, false, false, true);
    match result {
      MemValue(cap_bits, _) => {
        let _ = mem_write_value_meta(addr, cap_size, cap_bits, Version, Meta_Ver(v), false, false, false);
        MemValue()
      },
      MemException(e)  => internal_error("read of version during write failed")
    }
  }
}

function is_memory_version_OK(paddr : xlenbits, width : int) -> bool = {
  assert(width <= version_granule_size);
  match(CAP_AUTH_VERSION) {
    Some(cap_ver) => {
      if (cap_ver == cap_unversioned)
      then true /* no need to check memory version */
      else {
        let tag_addr1 = addr_to_tag_addr(paddr);
        let mem_ver = truncate(MEMr_tag_byte(EXTZ(tag_addr1)), cap_version_width);
        if mem_ver == cap_ver
        then {
          /* check possible second granule of access spanning two granules */
          let paddr2 = paddr + width - 1;
          let tag_addr2 = addr_to_tag_addr(paddr2);
          if (tag_addr1 == tag_addr2)
          then true /* single granule -- all good */
          else {
            let mem_ver2 = truncate(MEMr_tag_byte(EXTZ(tag_addr2)), cap_version_width);
            if mem_ver2 == cap_ver
            then true /* both granules OK */
            else false 
          }
        }
        else false
      }
    },
    None() => internal_error("No cap auth version to check.")
  }
}

function ext_check_phys_mem_read(t, paddr, width, aq, rl, res, meta) = {
  if t == Execute() 
  then Ext_PhysAddr_OK() /* Instruction fetch exempt from version checks */
  else if is_memory_version_OK(paddr, width)
  then Ext_PhysAddr_OK()
  else Ext_PhysAddr_Error(E_Extension(EXC_VERSION_FAULT))
}

function ext_check_phys_mem_write(wk, paddr, width, data, meta) = {
  if is_memory_version_OK(paddr, width)
  then Ext_PhysAddr_OK()
  else Ext_PhysAddr_Error(E_Extension(EXC_VERSION_FAULT))
}