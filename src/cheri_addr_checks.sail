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
  if cheri_registers_enabled() then getCapMode(PCC) else IntPtrMode
}

/* Pack trap information into form presented by XTVAL */

val encode_cheri_tval : (CapCheckType, CapEx) -> xlenbits
function encode_cheri_tval(typ, ex) =
  zeros(sizeof(xlen - 20)) @ capchecktype_code(typ) @ zeros(12) @ capex_code(ex)

/* Error handlers for address check errors */

val handle_cheri_exception : (CapCheckType, CapEx) -> unit
function handle_cheri_exception(capCheckType, capEx) =
  {
    if get_config_print_platform()
    then print_platform("CHERI " ^ capchecktype_name(capCheckType) ^
                        capex_name(capEx));
    let t : sync_exception = struct {
      trap    = E_Extension(EXC_CHERI),
      excinfo = Some(encode_cheri_tval(capCheckType, capEx)),
      ext     = None()
    };
    set_next_pc(exception_handler(cur_privilege(), CTL_TRAP(t), PC))
  }

val pcc_access_system_regs : unit -> bool
function pcc_access_system_regs () = canASR(PCC) | debug_mode_active

/* CHERI fetch address checks */

type ext_fetch_addr_error = CapEx

val ext_fetch_check_pc : (xlenbits, xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error)
function ext_fetch_check_pc(start_pc, pc) = {
  if debug_mode_active then Ext_FetchAddr_OK(pc)
  else if start_pc == pc
  then {
    /* We need to perform the permission checks only for the first granule. */
    if      not(capTaggedAndReservedValid(PCC))
    then    Ext_FetchAddr_Ext_Error(CapEx_TagViolation)
    else if capIsSealed(PCC)
    then    Ext_FetchAddr_Ext_Error(CapEx_SealViolation)
    else if not(canX(PCC))
    then    Ext_FetchAddr_Ext_Error(CapEx_PermissionViolation)
    else if not(validAddr(pc) | capBoundsInfinite(PCC))
    then    Ext_FetchAddr_Ext_Error(CapEx_InvalidAddressViolation)
    else if not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Ext_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(pc)
  } else {
    /* Perform only the valid address and bounds checks on the current granule, i.e. pc. */
    // For the second granule (the upper 2 bytes), check the *end* of the
    // address range is valid. Technically this should be equivalent to
    // checking pc, since it must be 2 byte aligned.
    if      not(validAddr(pc + 1) | capBoundsInfinite(PCC))
    then    Ext_FetchAddr_Ext_Error(CapEx_InvalidAddressViolation)
    else if not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Ext_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(pc)
  }
}

function ext_handle_fetch_check_error(err : ext_fetch_addr_error) -> unit = {
  let capEx = err;
  handle_cheri_exception(CapCheckType_Inst, capEx)
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
  else    Ext_ControlAddr_OK(target)
}

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  if      not(validAddr(pc) | capBoundsInfinite(PCC))
  then    Ext_ControlAddr_Error(CapEx_InvalidAddressViolation)
  else if not(inCapBounds(PCC, pc, min_instruction_bytes ()))
  then    Ext_ControlAddr_Error(CapEx_LengthViolation)
  else    Ext_ControlAddr_OK(pc)
}

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit = {
  let capEx = err;
  handle_cheri_exception(CapCheckType_JBr, capEx)
}

/* CHERI data address checks */

type ext_data_addr_error = CapEx

/*!
 * For given base register and offset returns, depending on current capability
 * mode flag, a bounding capability and effective address.
 */
val get_cheri_mode_cap_addr : (regidx, xlenbits) -> (Capability, xlenbits)
function get_cheri_mode_cap_addr (base_reg : regidx, offset : xlenbits) =
  match effective_cheri_mode() {
    CapPtrMode => (C(base_reg), C(base_reg).address + offset),
    IntPtrMode => (ddc, X(base_reg) + offset)
  }

function ext_data_get_addr(base_reg : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : range(0, max_mem_access))
         -> (xlenbits, Ext_DataAddr_Check(ext_data_addr_error)) = {
  let (auth_val, newAddr) = get_cheri_mode_cap_addr(base_reg, offset);

  let (have_rqd_load_perm, have_rqd_store_perm, have_rqd_asr_perm) : (bool, bool, bool) = match acc {
    Read(Data)            => (canR(auth_val), true          , true),
    Write(Data)           => (true          , canW(auth_val), true),
    ReadWrite(Data, Data) => (canR(auth_val), canW(auth_val), true),
    Cache(Data)           => (canR(auth_val), canW(auth_val), true),
    CacheInval(Data)      => (canR(auth_val), canW(auth_val), canASR(auth_val)),
    Cache(_)              => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Cache(_)"),
    CacheInval(_)         => internal_error(__FILE__, __LINE__, "ext_data_get_addr for CacheInval(_)"),
    Execute()             => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Execute"),
    Read(_)               => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Read(_)"),
    Write(_)              => internal_error(__FILE__, __LINE__, "ext_data_get_addr for Write(_)"),
    ReadWrite(_, _)       => internal_error(__FILE__, __LINE__, "ext_data_get_addr for ReadWrite(_, _)")
  };

  let any_byte_in_bounds: bool = match acc {
    Cache(Data)       => true,
    CacheInval(Data)  => true,
    _                 => false
  };

  ( newAddr
  , if not(capTaggedAndReservedValid(auth_val)) then
      Ext_DataAddr_Error(CapEx_TagViolation)
    else if capIsSealed(auth_val) then
      Ext_DataAddr_Error(CapEx_SealViolation)
    else if not(have_rqd_load_perm) then
      Ext_DataAddr_Error(CapEx_PermissionViolation)
    else if not(have_rqd_store_perm) then
      Ext_DataAddr_Error(CapEx_PermissionViolation)
    else if not(have_rqd_asr_perm) then
      Ext_DataAddr_Error(CapEx_PermissionViolation)
    // For loads/stores we need to check the entire range is valid addresses.
    else if not(validAddrRange(newAddr, width) | capBoundsInfinite(auth_val)) then
      Ext_DataAddr_Error(CapEx_InvalidAddressViolation)
    else if any_byte_in_bounds & not(anyByteInCapBounds(auth_val, newAddr, width)) then
      Ext_DataAddr_Error(CapEx_LengthViolation)
    else if not(any_byte_in_bounds) & not(inCapBounds(auth_val, newAddr, width)) then
      Ext_DataAddr_Error(CapEx_LengthViolation)
    else
      Ext_DataAddr_OK()
  )
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  let capEx = err;
  handle_cheri_exception(CapCheckType_Data, capEx)
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
  handle_cheri_exception(CapCheckType_Inst, CapEx_PermissionViolation)

/* Require ASR on any CSR that is not "unprivileged", i.e. accessible from U mode
  The exception for this is Zstid CSRs which always require ASR on writes and never require
  ASR on reads */
function requires_ASR_perm (csrno : bits(12), isWrite : bool) -> bool = {
  if is_zstid_csr(csrno) then return isWrite;
  not(check_CSR_priv(csrno, User))
}

function ext_check_CSR (csrno : bits(12), p : Privilege, isWrite : bool) -> bool = {
  pcc_access_system_regs() | not(requires_ASR_perm(csrno, isWrite))
}

function ext_check_CSR_fail () -> unit =
  handle_cheri_exception(CapCheckType_Inst, CapEx_PermissionViolation)
