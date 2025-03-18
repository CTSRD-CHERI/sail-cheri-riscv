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
  capEx          : CapEx,
  virtaddr(addr) : virtaddr,
) -> unit = {
  if get_config_print_platform()
  then print_platform("CHERI " ^ capchecktype_name(capCheckType) ^
                      capex_name(capEx));

  let t : sync_exception = struct {
    trap    = E_Extension(EXC_CHERI),
    excinfo = Some(convertInvalidAddr(addr)),
    ext     = Some(
      [Mk_Tval2(zeros()) with
        TYPE = capchecktype_code(capCheckType),
        CAUSE = capex_code(capEx),
      ]
    ),
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
    if      not(capTaggedAndReservedValid(auth_cap))
    then    Ext_FetchAddr_Ext_Error(CapEx_TagViolation)
    else if capIsSealed(auth_cap)
    then    Ext_FetchAddr_Ext_Error(CapEx_SealViolation)
    else if not(canX(auth_cap))
    then    Ext_FetchAddr_Ext_Error(CapEx_PermissionViolation)
    else if not(validAddr(addr) | capBoundsInfinite(auth_cap))
    then    Ext_FetchAddr_Ext_Error(CapEx_InvalidAddressViolation)
    else if not(inCapBounds(auth_cap, addr, len))
    then    Ext_FetchAddr_Ext_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(virtaddr(addr))
  } else {
    /* Perform only the valid address and bounds checks on the current granule, i.e. addr. */
    // For the second granule (the upper 2 bytes), check the *end* of the
    // address range is valid. Technically this should be equivalent to
    // checking addr, since it must be 2 byte aligned.
    if      not(validAddr(addr + 1) | capBoundsInfinite(auth_cap))
    then    Ext_FetchAddr_Ext_Error(CapEx_InvalidAddressViolation)
    else if not(inCapBounds(auth_cap, addr, len))
    then    Ext_FetchAddr_Ext_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(virtaddr(addr))
  }
}

function ext_fetch_check_pc(start_pc : xlenbits, pc : xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error) =
  cheri_fetch_addr_check(start_pc, pc, PCC, 2)

function ext_handle_fetch_check_error(err : ext_fetch_addr_error) -> unit = {
  let capEx = err;
  handle_cheri_exception(CapCheckType_Inst, capEx, virtaddr(zeros()))
}

/* CHERI control address checks */

type ext_control_addr_error = CapEx

/* the control address is derived from a non-PC register, e.g. in JALR */
function ext_control_check_addr(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  let target : xlenbits = [pc with 0=bitzero];

  if      not(validAddr(target) | capBoundsInfinite(PCC))
  then    Ext_ControlAddr_Error(CapEx_InvalidAddressViolation)
  else if not(inCapBounds(PCC, target, min_instruction_bytes ()))
  then    Ext_ControlAddr_Error(CapEx_LengthViolation)
  else    Ext_ControlAddr_OK(virtaddr(target))
}

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  if      not(validAddr(pc) | capBoundsInfinite(PCC))
  then    Ext_ControlAddr_Error(CapEx_InvalidAddressViolation)
  else if not(inCapBounds(PCC, pc, min_instruction_bytes ()))
  then    Ext_ControlAddr_Error(CapEx_LengthViolation)
  else    Ext_ControlAddr_OK(virtaddr(pc))
}

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit = {
  let capEx = err;
  handle_cheri_exception(CapCheckType_JBr, capEx, virtaddr(zeros()))
}

/* CHERI data address checks */

struct ExtDataErr = {
  cause: CapEx,
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
    CapPtrMode => (C(base_reg), virtaddr(C(base_reg).address + offset)),
    IntPtrMode => (ddc, virtaddr(X(base_reg) + offset)),
  }

function ext_data_get_addr(base_reg : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : range(0, max_mem_access))
         -> Ext_DataAddr_Check(ext_data_addr_error) = {
  let (auth_val, newAddr) = get_cheri_mode_cap_addr(base_reg, offset);

  let (have_rqd_load_perm, have_rqd_store_perm, have_rqd_asr_perm) : (bool, bool, bool) = match acc {
    Read(Data)        => (canR(auth_val), true          , true),
    Write(Data)       => (true          , canW(auth_val), true),
    ReadWrite(Data, Data) => (canR(auth_val), canW(auth_val), true),
    Cache(CleanFlush) => (canR(auth_val), canW(auth_val), true),
    Cache(Inval)      => (canR(auth_val), canW(auth_val), canASR(auth_val)),
    Cache(Zero)       => (true          , canW(auth_val), true),
    Execute()         => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Execute"),
    Read(Tagged)      => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Read(Tagged)"),
    Write(Tagged)     => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Write(Tagged)"),
    ReadWrite(_, _)   => internal_error(__FILE__, __LINE__, "ext_data_get_addr for ReadWrite(...)")
  };

  let newAddr = virtaddr_bits(newAddr);

  let (any_byte_in_bounds, exc_addr): (bool, xlenbits) = match acc {
    Cache(CleanFlush) => (true, newAddr - offset),
    Cache(Inval)      => (true, newAddr - offset),
    Cache(Zero)       => (false, newAddr - offset),
    _                 => (false, newAddr),
  };

  let error = if not(capTaggedAndReservedValid(auth_val)) then
    Some(CapEx_TagViolation)
  else if capIsSealed(auth_val) then
    Some(CapEx_SealViolation)
  else if not(have_rqd_load_perm) then
    Some(CapEx_PermissionViolation)
  else if not(have_rqd_store_perm) then
    Some(CapEx_PermissionViolation)
  else if not(have_rqd_asr_perm) then
    Some(CapEx_PermissionViolation)
  // For loads/stores we need to check the entire range is valid addresses.
  else if not(validAddrRange(newAddr, width) | capBoundsInfinite(auth_val)) then
    Some(CapEx_InvalidAddressViolation)
  else if any_byte_in_bounds & not(anyByteInCapBounds(auth_val, newAddr, width)) then
    Some(CapEx_LengthViolation)
  else if not(any_byte_in_bounds) & not(inCapBounds(auth_val, newAddr, width)) then
    Some(CapEx_LengthViolation)
  else
    None();

  match error {
    Some(cause) => Ext_DataAddr_Error(struct {cause = cause, addr = virtaddr(exc_addr)}),
    None() => Ext_DataAddr_OK(virtaddr(newAddr)),
  }
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  let capEx = err.cause;
  handle_cheri_exception(CapCheckType_Data, capEx, err.addr)
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
  handle_cheri_exception(CapCheckType_Inst, CapEx_PermissionViolation, virtaddr(zeros()))

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
    CHERIPermExc => handle_cheri_exception(CapCheckType_Inst, CapEx_PermissionViolation, virtaddr(zeros())),
    IllegalInstruction => handle_illegal(),
  };
}

function ext_pma_check (access_type : AccessType(ext_access_type), attributes : PMA) -> bool = {
  // Writes of tagged capabilities to untaggable memory optionally
  // cause an access fault. Otherwise they silently discard the tag.
  let access_fault = not(attributes.taggable) & attributes.taggableAccessFaults & isTaggedWrite(access_type);
  not(access_fault)
}
