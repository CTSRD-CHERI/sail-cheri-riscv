/* accessors for capability representation */

/* reads a given capability register, or the null capability if the argument is zero. */
val rC : forall 'n, 0 <= 'n < 32. regno('n) -> regtype effect {rreg, escape}
function rC r = {
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
    _  => internal_error("Invalid capability register")
  }
}

/* writes a register with a capability value */
val wC : forall 'n, 0 <= 'n < 32. (regno('n), regtype) -> unit effect {wreg, escape}
function wC (r, v) = {
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
    _  => internal_error("Invalid capability register")
  };
  if (r != 0) then {
     rvfi_wX(r, v.address);
     if get_config_print_reg() then
       print_reg("x" ^ string_of_int(r) ^ " <- " ^ RegStr(v));
  }
}

function rC_bits(r: bits(5)) -> regtype = rC(unsigned(r))

function wC_bits(r: bits(5), v: regtype) -> unit = wC(unsigned(r), v)

overload C = {rC_bits, wC_bits, rC, wC}

val ext_init_regs : unit -> unit effect {wreg}
function ext_init_regs () = {
  PCC = default_cap;
  DDC = default_cap;
  nextPCC = default_cap;

  UTCC = default_cap;
  UTDC = null_cap;
  UScratchC = null_cap;
  UEPCC = default_cap;

  STCC = default_cap;
  STDC = null_cap;
  SScratchC = null_cap;
  SEPCC = default_cap;

  MTCC = default_cap;
  MTDC = null_cap;
  MScratchC = null_cap;
  MEPCC = default_cap;

  x1  = null_cap;
  x2  = null_cap;
  x3  = null_cap;
  x4  = null_cap;
  x5  = null_cap;
  x6  = null_cap;
  x7  = null_cap;
  x8  = null_cap;
  x9  = null_cap;
  x10 = null_cap;
  x11 = null_cap;
  x12 = null_cap;
  x13 = null_cap;
  x14 = null_cap;
  x15 = null_cap;
  x16 = null_cap;
  x17 = null_cap;
  x18 = null_cap;
  x19 = null_cap;
  x20 = null_cap;
  x21 = null_cap;
  x22 = null_cap;
  x23 = null_cap;
  x24 = null_cap;
  x25 = null_cap;
  x26 = null_cap;
  x27 = null_cap;
  x28 = null_cap;
  x29 = null_cap;
  x30 = null_cap;
  x31 = null_cap;

  misa->X() = 0b1;
  sccsr->d() = 0b1;
  sccsr->e() = 0b1;
  uccsr->d() = 0b1;
  uccsr->e() = 0b1;
}

/*!
 * This function is called after above when running rvfi and allows the model
 * to be initialised differently. For RVFI we initialise cap regs to default
 * instead of null.
 */
val ext_rvfi_init : unit -> unit effect {wreg}
function ext_rvfi_init () = {
  x1  = default_cap;
  x2  = default_cap;
  x3  = default_cap;
  x4  = default_cap;
  x5  = default_cap;
  x6  = default_cap;
  x7  = default_cap;
  x8  = default_cap;
  x9  = default_cap;
  x10 = default_cap;
  x11 = default_cap;
  x12 = default_cap;
  x13 = default_cap;
  x14 = default_cap;
  x15 = default_cap;
  x16 = default_cap;
  x17 = default_cap;
  x18 = default_cap;
  x19 = default_cap;
  x20 = default_cap;
  x21 = default_cap;
  x22 = default_cap;
  x23 = default_cap;
  x24 = default_cap;
  x25 = default_cap;
  x26 = default_cap;
  x27 = default_cap;
  x28 = default_cap;
  x29 = default_cap;
  x30 = default_cap;
  x31 = default_cap;
}

/* register names */

val cap_reg_name_abi : regidx -> string

function cap_reg_name_abi(r) = {
  match (r) {
    0b00000 => "cnull",
    _       => "c" ^ reg_name_abi(r)
  }
}

overload to_str = {cap_reg_name_abi}

/* mappings for assembly */

val cap_reg_name : bits(5) <-> string
mapping cap_reg_name = {
    0b00000 <-> "cnull",
    r       <-> "c" ^ reg_name(r)
}

mapping cap_creg_name : bits(3) <-> string = {
  r <-> "c" ^ creg_name(r)
}
