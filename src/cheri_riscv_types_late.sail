/*
 * Additional CHERI-specific types that can refer back to RISC-V's riscv_types
 */

/*
 * CHERI instructions occasionally let us override the processor's notion of
 * Privilege levels.  PrivDefault means "fall back to effectivePrivilege" while
 * PrivOverride explicitly specifies the desired privilege for the operation at
 * hand.
 *
 * Eventually something like this might appear in the base RISC-V model, as the
 * Hypervisor extension needs similar functionality.
 */
union OptPrivilege = {
  PrivDefault : unit,
  PrivOverride : Privilege
}
