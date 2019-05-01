/* Error handlers for address check errors */

val raise_c2_exception6 : (CapEx, bits(6)) -> bool effect {escape, rreg, wreg}
function raise_c2_exception6(capEx, regnum) =
  {
    print("CHERI " ^ string_of_capex(capEx) ^ " Reg=" ^ BitStr(regnum));
    let cause : cheri_cause = struct {
        cap_idx = regnum,
        capEx   = capEx
    };
    let t : sync_exception = struct {
      trap    = E_CHERI,
      excinfo = (None() : option(xlenbits)),
      ext     = Some(cause)
    };
    nextPC = handle_exception(cur_privilege, CTL_TRAP(t), PC);
    false
  }

/*!
causes the processor to raise a capability exception by writing the given capability exception cause and register number to the xccsr register then signalling an exception. */
val raise_c2_exception : (CapEx, bits(5)) -> bool effect {escape, rreg, wreg}
function raise_c2_exception(capEx, regnum) =
  let reg6 = 0b0 @ regnum in
  raise_c2_exception6(capEx, reg6)

/*!
is as [raise_c2_exception] except that CapCause.RegNum  is written with the special value 0x10 indicating PCC register.
 */
val raise_c2_exception_pcc : (CapEx) -> bool effect {escape, rreg, wreg}
function raise_c2_exception_pcc(capEx) =
  raise_c2_exception6(capEx, 0b100000)

val pcc_access_system_regs : unit -> bool effect {rreg}
function pcc_access_system_regs () = PCC.access_system_regs

/* CHERI fetch address checks */

type ext_fetch_addr_error = CapEx

val ext_fetch_check_pc : (xlenbits, xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error) effect {rreg}
function ext_fetch_check_pc(start_pc, pc) = {
  if   start_pc == pc
  then {
    /* We need to perform the permission checks only for the first granule. */
    if      not(PCC.tag)
    then    Ext_FetchAddr_Error(CapEx_TagViolation)
    else if PCC.sealed
    then    Ext_FetchAddr_Error(CapEx_SealViolation)
    else if not(PCC.permit_execute)
    then    Ext_FetchAddr_Error(CapEx_PermitExecuteViolation)
    else if not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(pc)
  } else {
    /* Perform only the bounds checks on the current granule, i.e. pc. */
    if      not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_LengthViolation)
    else    Ext_FetchAddr_OK(pc)
  }
}

function ext_handle_fetch_check_error(e : ext_fetch_addr_error) -> unit = {
  /* FIXME: check if we can avoid the ignored boolean return */
  /* FIXME: rename to be more risc-v friendly? */
  let _ = raise_c2_exception_pcc(e);
  ()
}

/* CHERI control address checks */

type ext_control_addr_error = (CapEx, bits(6)) // FIXME: use a type name for bits(6)

/* the control address is derived from a non-PC register, e.g. in JALR */
function ext_control_check_addr(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  let pcc_base = getCapBaseBits(PCC);
  /* We are given the addr without any bit[0] clearing, so the addition
   * below may include a set addr[0], and so the bounds checks should
   * be accurate.
   */
  let target : xlenbits = (pcc_base + pc)[63 .. 1] @ 0b0;
  if   not(inCapBounds(PCC, target, min_instruction_bytes ()))
  then Ext_ControlAddr_Error(CapEx_LengthViolation, 0b100000)  // FIXME: use a name for this cap_idx
  else Ext_ControlAddr_OK(target)
}

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  if   not(inCapBounds(PCC, pc, min_instruction_bytes ()))
  then Ext_ControlAddr_Error(CapEx_LengthViolation, 0b100000)  // FIXME: use a name for this cap_idx
  else Ext_ControlAddr_OK(pc)
}

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit = {
  let (capEx, regnum) = err;
  /* FIXME: check if we can avoid the ignored boolean return */
  /* FIXME: rename to be more risc-v friendly? */
  let _ = raise_c2_exception6(capEx, regnum);
  ()
}

/* CHERI data address checks */

type ext_data_addr_error = (CapEx, bits(6)) // FIXME: use a type name for bits(6)

function ext_data_check_addr(base_reg : regbits, addr : xlenbits, acc : AccessType, rt : ReadType, width : word_width)
         -> Ext_DataAddr_Check(ext_data_addr_error) = {
  /* If we are in capabiltiy mode then do address checks on the base register, 
     otherwise on DDC. Also offset address in latter case. */
  let (cap_val : Capability, newAddr : xlenbits, cause_regno : bits(6)) =
    if (PCC.flag_cap_mode) then
      (readCapReg(base_reg), addr, 0b0 @ base_reg)
    else
      let ddc = DDC in
      (ddc, ddc.address + addr, 0b100001);
  let have_rqd_load_perm : bool = match acc {
    Read       => cap_val.permit_load,
    Write      => true,
    ReadWrite  => cap_val.permit_load,
    Execute    => false /* should only be for load/store */
  };
  let have_rqd_store_perm : bool = match acc {
    Read       => true,
    Write      => cap_val.permit_store,
    ReadWrite  => cap_val.permit_store,
    Execute    => false /* should only be for load/store */
  };

  if not(cap_val.tag) then
    Ext_DataAddr_Error(CapEx_TagViolation, cause_regno)
  else if cap_val.sealed then
    Ext_DataAddr_Error(CapEx_SealViolation, cause_regno)
  else if not(have_rqd_load_perm) then
    Ext_DataAddr_Error(CapEx_PermitLoadViolation, cause_regno)
  else if not(have_rqd_store_perm) then
    Ext_DataAddr_Error(CapEx_PermitStoreViolation, cause_regno)
  else if not(inCapBounds(cap_val, newAddr, word_width_bytes(width))) then
    Ext_DataAddr_Error(CapEx_LengthViolation, cause_regno)
  else
    Ext_DataAddr_OK(newAddr)
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  let (capEx, regnum) = err;
  /* FIXME: check if we can avoid the ignored boolean return */
  /* FIXME: rename to be more risc-v friendly? */
  let _ = raise_c2_exception6(capEx, regnum);
  ()
}


/* accessors for default architectural addresses, for use from within instructions */
/* FIXME: these don't really belong in this file. */

/* FIXME: The asymmetry between get_next_pc and set_next_pc where one
 * returns the architectural PC but the other set the PCC-relative PC
 * is a bit weird. The way they are currently used it is correct but
 * we should either rename one of the functions or call set_next_pc
 * with the original target address instead of the munged one. - RNW.
 */

val get_next_pc : unit -> xlenbits effect {rreg}
function get_next_pc() =
  nextPC - getCapBaseBits(PCC)

val set_next_pc : xlenbits -> unit effect {wreg}
function set_next_pc(pc) =
  /* could check for internal errors here on invalid pc */
  nextPC = pc

val tick_pc : unit -> unit effect {rreg, wreg}
function tick_pc() = {
  PCC = nextPCC;
  PC = nextPC
}
