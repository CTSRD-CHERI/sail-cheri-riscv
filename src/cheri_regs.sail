/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* accessors for capability representation */

/* reads a given capability register, or the null capability if the argument is zero. */
function rC(r : regno) -> regtype = {
  match r {
    0  => zero_reg,
    1  => x1,
    2  => x2,
    3  => x3,
    4  => x4,
    5  => x5,
    6  => x6,
    7  => x7,
    8  => x8,
    9  => x9,
    10 => x10,
    11 => x11,
    12 => x12,
    13 => x13,
    14 => x14,
    15 => x15,
    16 => x16,
    17 => x17,
    18 => x18,
    19 => x19,
    20 => x20,
    21 => x21,
    22 => x22,
    23 => x23,
    24 => x24,
    25 => x25,
    26 => x26,
    27 => x27,
    28 => x28,
    29 => x29,
    30 => x30,
    31 => x31,
    _  => internal_error(__FILE__, __LINE__, "Invalid capability register")
  }
}

/* writes a register with a capability value */
function wC (r : regno, v : regtype) -> unit = {
  match r {
    0  => (),
    1  => x1 = v,
    2  => x2 = v,
    3  => x3 = v,
    4  => x4 = v,
    5  => x5 = v,
    6  => x6 = v,
    7  => x7 = v,
    8  => x8 = v,
    9  => x9 = v,
    10 => x10 = v,
    11 => x11 = v,
    12 => x12 = v,
    13 => x13 = v,
    14 => x14 = v,
    15 => x15 = v,
    16 => x16 = v,
    17 => x17 = v,
    18 => x18 = v,
    19 => x19 = v,
    20 => x20 = v,
    21 => x21 = v,
    22 => x22 = v,
    23 => x23 = v,
    24 => x24 = v,
    25 => x25 = v,
    26 => x26 = v,
    27 => x27 = v,
    28 => x28 = v,
    29 => x29 = v,
    30 => x30 = v,
    31 => x31 = v,
    _  => internal_error(__FILE__, __LINE__, "Invalid capability register")
  };
  if (r != 0) then {
     rvfi_wX(r, v.address);
     if get_config_print_reg() then
       print_reg("x" ^ dec_str(r) ^ " <- " ^ RegStr(v));
  }
}

function rC_bits(r: regidx) -> regtype = rC(unsigned(r))

function wC_bits(r: regidx, v: regtype) -> unit = wC(unsigned(r), v)

overload C = {rC_bits, wC_bits, rC, wC}

/*!
 * This function is called after above when running rvfi and allows the model
 * to be initialised differently. For RVFI we initialise cap regs to default
 * instead of null.
 */
val ext_rvfi_reset : unit -> unit
function ext_rvfi_reset () = {
  x1  = infinite_cap;
  x2  = infinite_cap;
  x3  = infinite_cap;
  x4  = infinite_cap;
  x5  = infinite_cap;
  x6  = infinite_cap;
  x7  = infinite_cap;
  x8  = infinite_cap;
  x9  = infinite_cap;
  x10 = infinite_cap;
  x11 = infinite_cap;
  x12 = infinite_cap;
  x13 = infinite_cap;
  x14 = infinite_cap;
  x15 = infinite_cap;
  x16 = infinite_cap;
  x17 = infinite_cap;
  x18 = infinite_cap;
  x19 = infinite_cap;
  x20 = infinite_cap;
  x21 = infinite_cap;
  x22 = infinite_cap;
  x23 = infinite_cap;
  x24 = infinite_cap;
  x25 = infinite_cap;
  x26 = infinite_cap;
  x27 = infinite_cap;
  x28 = infinite_cap;
  x29 = infinite_cap;
  x30 = infinite_cap;
  x31 = infinite_cap;
}

/* mappings for assembly */

val cap_reg_name : regidx <-> string
mapping cap_reg_name = {
    0b00000 <-> "cnull",
    r       <-> "c" ^ reg_name(r)
}

mapping cap_creg_name : bits(3) <-> string = {
  r <-> "c" ^ creg_name(r)
}

// Modify a capability when storing in a register that cannot store all invalid
// addresses. The address may need to be changed, and if that happens the
// tag may be cleared.
function convertInvalidAddrCap(cap : Capability) -> Capability = {
  // Convert invalid addresses that can't be stored to invalid addresses that can.
  let reducedAddr = convertInvalidAddr(cap.address);
  // If conversion was required, then use scaddr semantics which clears the tag if it's sealed or was not representable.
  let cap = if reducedAddr != cap.address then setCapAddrChecked(cap, reducedAddr) else cap;
  // Clear the tag if the address is invalid without infinite bounds, even if it didn't change from conversion
  clearTagIf(cap, not(validAddr(cap.address) | capBoundsInfinite(cap)))
}

// Add illegal address conversion for capabilities to the overload.
overload convertInvalidAddr = {convertInvalidAddrCap}
