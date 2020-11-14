/* Error handlers for address check errors */

val handle_cheri_cap_exception : (CapEx, capreg_idx) -> unit effect {escape, rreg, wreg}
function handle_cheri_cap_exception(capEx, regnum) =
  {
    print("CHERI " ^ string_of_capex(capEx) ^ " Reg=" ^ BitStr(regnum));
    let cause : cheri_cause = struct {
        cap_idx = regnum,
        capEx   = capEx
    };
    let t : sync_exception = struct {
      trap    = E_Extension(EXC_CHERI),
      excinfo = Some(EXTZ(regnum @ CapExCode(capEx)) : xlenbits),
      ext     = Some(cause)
    };
    set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC))
  }

/*!
 * Causes the processor to raise a capability exception by writing the given
 * capability exception cause and register number to the xccsr register then
 * signalling an exception.
 */
val handle_cheri_reg_exception : (CapEx, regidx) -> unit effect {escape, rreg, wreg}
function handle_cheri_reg_exception(capEx, regnum) =
  let reg6 = 0b0 @ regnum in
  handle_cheri_cap_exception(capEx, reg6)

/*!
 * Is as [handle_cheri_cap_exception] except that the capability register
 * number uses the special value 0x10 indicating the PCC register.
 */
val handle_cheri_pcc_exception : (CapEx) -> unit effect {escape, rreg, wreg}
function handle_cheri_pcc_exception(capEx) =
  handle_cheri_cap_exception(capEx, 0b100000)

val pcc_access_system_regs : unit -> bool effect {rreg}
function pcc_access_system_regs () = PCC.access_system_regs

/* CHERI fetch address checks */

type ext_fetch_addr_error = CapEx

val ext_fetch_check_pc : (xlenbits, xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error) effect {rreg}
function ext_fetch_check_pc(start_pc, pc) = {
  if   start_pc == pc
  then {
    pcc_base = getCapBaseBits(PCC);
    /* We need to perform the permission checks only for the first granule. */
    if      not(PCC.tag)
    then    Ext_FetchAddr_Error(CapEx_TagViolation)
    else if isCapSealed(PCC)
    then    Ext_FetchAddr_Error(CapEx_SealViolation)
    else if not(PCC.permit_execute)
    then    Ext_FetchAddr_Error(CapEx_PermitExecuteViolation)
    else if not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_LengthViolation)
    /* Require that PCC.base be as aligned as PC. This
       is also enforced when setting PCC in most places. */
    else if pcc_base[0] != bitzero | (pcc_base[1] != bitzero & ~(haveRVC()))
    then    Ext_FetchAddr_Error(CapEx_UnalignedBase)
    else    Ext_FetchAddr_OK(pc)
  } else {
    /* Perform only the bounds checks on the current granule, i.e. pc. */
    if      not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(pc)
  }
}

function ext_handle_fetch_check_error(e : ext_fetch_addr_error) -> unit =
  handle_cheri_pcc_exception(e)

/* CHERI control address checks */

type ext_control_addr_error = (CapEx, capreg_idx)

/* the control address is derived from a non-PC register, e.g. in JALR */
function ext_control_check_addr(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  let pcc_base = getCapBaseBits(PCC);
  /* We are given the addr without any bit[0] clearing, so the addition
   * below may include a set addr[0], and so the bounds checks should
   * be accurate.
   */
  let target : xlenbits = [pcc_base + pc with 0=bitzero];
  if   not(inCapBounds(PCC, target, min_instruction_bytes ()))
  then Ext_ControlAddr_Error(CapEx_LengthViolation, PCC_IDX)
  else Ext_ControlAddr_OK(target)
}

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  if   not(inCapBounds(PCC, pc, min_instruction_bytes ()))
  then Ext_ControlAddr_Error(CapEx_LengthViolation, PCC_IDX)
  else Ext_ControlAddr_OK(pc)
}

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit = {
  let (capEx, regnum) = err;
  handle_cheri_cap_exception(capEx, regnum)
}

/* CHERI data address checks */

type ext_data_addr_error = (CapEx, capreg_idx)


/*!
 * For given base register and offset returns, depending on current capability
 * mode flag, a bounding capability, effective address, and capreg_idx (for use
 * in cap cause).
 */
val get_cheri_mode_cap_addr : (regidx, xlenbits) -> (Capability, xlenbits, capreg_idx) effect {rreg, escape}
function get_cheri_mode_cap_addr (base_reg : regidx, offset : xlenbits) = {
  if (PCC.flag_cap_mode) then
    let base_cap = C(base_reg) in
    (base_cap, base_cap.address + offset, 0b0 @ base_reg)
  else
    let ddc = DDC in
    (ddc, ddc.address + X(base_reg) + offset, DDC_IDX);
}

function ext_data_get_addr(base_reg : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : word_width)
         -> Ext_DataAddr_Check(ext_data_addr_error) = {

  let (auth_val, newAddr, auth_idx) = get_cheri_mode_cap_addr(base_reg, offset);

  let (have_rqd_load_perm, have_rqd_store_perm) : (bool, bool) = match acc {
    Read(Data)            => (auth_val.permit_load, true                 ),
    Write(Data)           => (true                , auth_val.permit_store),
    ReadWrite(Data, Data) => (auth_val.permit_load, auth_val.permit_store),
    Execute()             => internal_error("ext_data_get_addr for Execute"),
    Read(_)               => internal_error("ext_data_get_addr for Read(_)"),
    Write(_)              => internal_error("ext_data_get_addr for Write(_)"),
    ReadWrite(_, _)       => internal_error("ext_data_get_addr for ReadWrite(_, _)")
  };

  if not(auth_val.tag) then
    Ext_DataAddr_Error(CapEx_TagViolation, auth_idx)
  else if isCapSealed(auth_val) then
    Ext_DataAddr_Error(CapEx_SealViolation, auth_idx)
  else if not(have_rqd_load_perm) then
    Ext_DataAddr_Error(CapEx_PermitLoadViolation, auth_idx)
  else if not(have_rqd_store_perm) then
    Ext_DataAddr_Error(CapEx_PermitStoreViolation, auth_idx)
  else if not(inCapBounds(auth_val, newAddr, word_width_bytes(width))) then
    Ext_DataAddr_Error(CapEx_LengthViolation, auth_idx)
  else
    Ext_DataAddr_OK(newAddr)
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  let (capEx, regnum) = err;
  handle_cheri_cap_exception(capEx, regnum)
}


/* Is XRET from given mode permitted by extension? */
function ext_check_xret_priv (p : Privilege) : Privilege -> bool =
  pcc_access_system_regs()

/* Called if above check fails */
function ext_fail_xret_priv () : unit -> unit = 
  handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation)

function ext_check_CSR (csrno : bits(12), p : Privilege, isWrite : bool) -> bool =
  pcc_access_system_regs() /* XXX need to make this more granular e.g. a whitelist of allowed CSR
  accesses */

function ext_check_CSR_fail () -> unit =
  handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation)
