/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Returns the current CHERI execution mode */

val effective_cheri_mode : unit -> ExecutionMode
function effective_cheri_mode() = {
  // if debug_mode_active then return getCapMode(dinfc);

  if cheri_registers_enabled() then getCapMode(PCC) else IntPtrMode
}

/* Error handlers for address check errors */

function handle_cheri_exception(
  capCheckType   : CapCheckType,
  virtaddr(addr) : virtaddr,
) -> unit = {
  if get_config_print_platform()
  then print_platform("CHERI " ^ capchecktype_name(capCheckType));

  let t : sync_exception = struct {
    trap    = E_Extension(EXC_CHERI(capCheckType)),
    excinfo = Some(convertInvalidAddr(addr)),
  };
  set_next_pc(exception_handler(cur_privilege(), CTL_TRAP(t), PC))
}

val pcc_access_system_regs : unit -> bool
function pcc_access_system_regs () = canASR(PCC)

/* CHERI fetch address checks */

function cheri_fetch_addr_check(start_addr : xlenbits, addr : xlenbits, auth_cap : Capability, len : CapLenInt) -> Ext_FetchAddr_Check(ext_fetch_addr_error) = {
  if debug_mode_active then Ext_FetchAddr_OK(virtaddr(addr))
  else if start_addr == addr
  then {
    /* We need to perform the permission checks only for the first granule. */
    if  capTaggedAndReservedValid(auth_cap) &
        not(capIsSealed(auth_cap)) &
        canX(auth_cap) &
        (validAddr(addr) | capBoundsInfinite(auth_cap)) &
        inCapBounds(auth_cap, addr, len)
    then Ext_FetchAddr_OK(virtaddr(addr))
    else Ext_FetchAddr_Ext_Error()
  } else {
    /* Perform only the valid address and bounds checks on the current granule, i.e. addr. */
    // For the second granule (the upper 2 bytes), check the *end* of the
    // address range is valid. Technically this should be equivalent to
    // checking addr, since it must be 2 byte aligned.
    if  (validAddr(addr + 1) | capBoundsInfinite(auth_cap)) &
        inCapBounds(auth_cap, addr, len)
    then Ext_FetchAddr_OK(virtaddr(addr))
    else Ext_FetchAddr_Ext_Error()
  }
}

function ext_fetch_check_pc(start_pc : xlenbits, pc : xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error) =
  cheri_fetch_addr_check(start_pc, pc, PCC, 2)

function ext_handle_fetch_check_error(err : ext_fetch_addr_error) -> unit = {
  handle_cheri_exception(CapCheckType_Inst(), virtaddr(zeros()))
}

/* CHERI data address checks */

struct ExtDataErr = {
  cause: CapCheckType,
  addr: virtaddr,
}

type ext_data_addr_error = ExtDataErr

/*!
 * For given base register and offset returns, depending on current capability
 * mode flag, a bounding capability and effective address.
 */
val get_cheri_mode_cap_addr : (regidx, xlenbits) -> (Capability, virtaddr)
function get_cheri_mode_cap_addr (base_reg : regidx, offset : xlenbits) =
  match effective_cheri_mode() {
    CapPtrMode => (Y(base_reg), virtaddr(Y(base_reg).address + offset)),
    IntPtrMode => (ddc, virtaddr(X(base_reg) + offset)),
  }

function ext_data_get_addr(base_reg : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : range(0, max_mem_access))
         -> Ext_DataAddr_Check(ext_data_addr_error) = {
  let (auth_val, newAddr) = get_cheri_mode_cap_addr(base_reg, offset);

  let (have_rqd_load_perm, have_rqd_store_perm, have_rqd_asr_perm, cause) : (bool, bool, bool, CapCheckType) = match acc {
    Read(Data)        => (canR(auth_val), true          , true, CapCheckType_Ld()),
    Write(Data)       => (true          , canW(auth_val), true, CapCheckType_St()),
    ReadWrite(Data, Data) => (canR(auth_val), canW(auth_val), true, CapCheckType_St()),
    Cache(CleanFlush) => (canR(auth_val), canW(auth_val), true, CapCheckType_St()),
    Cache(Inval)      => (canR(auth_val), canW(auth_val), pcc_access_system_regs(), CapCheckType_St()),
    Cache(Zero)       => (true          , canW(auth_val), true, CapCheckType_St()),
    Execute()         => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Execute"),
    Read(Tagged)      => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Read(Tagged)"),
    Write(Tagged)     => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Write(Tagged)"),
    ReadWrite(_, _)   => internal_error(__FILE__, __LINE__, "ext_data_get_addr for ReadWrite(...)")
  };

  let newAddr = virtaddr_bits(newAddr);

  let (any_byte_in_bounds, exc_addr): (bool, xlenbits) = match acc {
    Cache(CleanFlush) => (true, newAddr - offset),
    Cache(Inval)      => (false, newAddr - offset),
    Cache(Zero)       => (false, newAddr - offset),
    _                 => (false, newAddr),
  };

  if  capTaggedAndReservedValid(auth_val) &
      not(capIsSealed(auth_val)) &
      have_rqd_load_perm &
      have_rqd_store_perm &
      have_rqd_asr_perm &
      // For loads/stores we need to check the entire range is valid addresses.
      (validAddrRange(newAddr, width) | capBoundsInfinite(auth_val)) &
      anyByteInCapBounds(auth_val, newAddr, width) &
      (any_byte_in_bounds | inCapBounds(auth_val, newAddr, width))
  then Ext_DataAddr_OK(virtaddr(newAddr))
  else Ext_DataAddr_Error(struct {cause = cause, addr = virtaddr(exc_addr)})
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  handle_cheri_exception(err.cause, err.addr)
}

/* Default implementations of these hooks permit all accesses.  */
function ext_check_phys_mem_read (access_type, paddr, size, aquire, release, reserved, read_meta) =
  Ext_PhysAddr_OK()

function ext_check_phys_mem_write(write_kind, paddr, size, data, metadata) =
  Ext_PhysAddr_OK()

/* Is XRET from given mode permitted by extension? */
function ext_check_xret_priv (p : Privilege) : Privilege -> bool = {
  pcc_access_system_regs()
}

/* Called if above check fails */
function ext_fail_xret_priv () : unit -> unit =
  handle_cheri_exception(CapCheckType_Inst(), virtaddr(zeros()))

/* Require ASR on any CSR that is not "unprivileged", i.e. accessible from U mode
  The exception for this is Zstid CSRs which always require ASR on writes and never require
  ASR on reads */
function requires_ASR_perm (csrno : bits(12), isWrite : bool) -> bool = {
  if is_zstid_csr(csrno) then return isWrite;
  not(check_CSR_priv(csrno, User))
}

// Types of exception from CSR accesses that ext_check_CSR() can raise
enum ext_csr_exc_type = {
  CHERIPermExc,
  IllegalInstruction,
}

function ext_check_CSR (csrno : bits(12), p : Privilege, isWrite : bool, op : csrop, is_imm : bool) -> option(ext_csr_exc_type) =
  if not(pcc_access_system_regs()) & requires_ASR_perm(csrno, isWrite) then Some(CHERIPermExc)
  else None()

function ext_check_CSR_fail (fail_type : ext_csr_exc_type) -> unit = {
  match fail_type {
    CHERIPermExc => handle_cheri_exception(CapCheckType_Inst(), virtaddr(zeros())),
    IllegalInstruction => handle_illegal(),
  };
}

function ext_pma_check (access_type : AccessType(ext_access_type), attributes : PMA) -> bool = {
  // Writes of tagged capabilities to untaggable memory optionally
  // cause an access fault. Otherwise they silently discard the tag.
  let access_fault = not(attributes.taggable) & attributes.taggableAccessFaults & isTaggedWrite(access_type);
  not(access_fault)
}
