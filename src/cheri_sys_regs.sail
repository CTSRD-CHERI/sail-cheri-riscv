/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* CHERI CSRs */

// Unlike the other registers which completely replace the old XLEN ones,
// PCC is split across this and the XLEN PC register.
// TODO: It would be much cleaner to not store half of PCC in PC; instead
// we should always access PC via `get_arch_pc()` (or similar) and then
// override that for CHERI to return `PCC.address`. See get_mepc() for example.
register PCC       : Capability
register nextPCC   : Capability

register ddc_y      : Capability
register stvec_y    : Capability
register sscratch_y : Capability = null_cap
register sepc_y     : Capability
register mtid_y     : Capability = null_cap
register stid_y     : Capability = null_cap
register utid_y     : Capability = null_cap
register mtvec_y    : Capability
register mscratch_y : Capability = null_cap
register mepc_y     : Capability

/* Cheri pcc helpers */

// Return the minimum number of bytes in an instruction supported
// by the implementation. If writable misa is supported then
// this returns 2 irrespective of the value of misa[C].
function min_instruction_bytes() -> CapAddrInt = if sys_enable_rvc() then 2 else 4

// Defined in riscv_sys_control.sail
val feature_enabled_for_priv : (Privilege, bit, bit) -> bool

/* Checking whether the Xcheri extension is enabled */
function cheri_registers_enabled () -> bool = {
  // CRE is always 1 in debug mode
  if debug_mode_active then return true;
  // CRE logic described in CHERI spec
  mseccfg[CRE] == 0b1
    & feature_enabled_for_priv(cur_privilege(), menvcfg[CRE][0], senvcfg[CRE][0])
}

function haveZstid () -> bool = true

/*
 * Used during readout (but not assignment!) of ?EPC registers (csrrw,
 * handle_trap_extension) and not during control transfer
 * (get_xreg_target).
 *
 * The result is that it is only possible to faithfully read out ?EPC if
 * either
 *  - misa.C is enabled or
 *  - misa.C is disabled and the EPC offset is sufficiently aligned
 *
 * If misa.C is held constant, as it almost always will be, between fault and
 * readback, ?EPC will be faithfully read back, because the alignment will
 * adhere to the requirements of the architecture, which is what legalization
 * is intending to enforce.
 *
 * If neither of those conditions hold, the resulting readout will be a lie; if
 * ?EPC has additionally been set to be a sentry, then the result will be an
 * untagged lie.
 *
 * NOTE: this legalisation is also used for DPCC in the Sdext extension
 */
function legalize_epc_y(v : Capability) -> Capability = {
  let int_val = v.address;
  let legalized = legalize_xepc(int_val);

  if   legalized == int_val
  then v /* avoid possibly attempting to set the offset of a sentry */
  else setCapAddrChecked(v, legalized)
}
