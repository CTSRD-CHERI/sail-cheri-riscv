/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

let cap_max_addr = MAX(cap_addr_width)
let cap_max_otype = MAX(cap_otype_width) - reserved_otypes

type cap_uperms_shift : Int = 15
let  cap_uperms_shift = sizeof(cap_uperms_shift)
type cap_perms_width : Int = cap_uperms_shift + cap_uperms_width
let  cap_perms_width = sizeof(cap_perms_width)

type CapAddrBits  = bits(cap_addr_width)
type CapAddrInt   = range(0, (2 ^ cap_addr_width) - 1)
type CapLenBits   = bits(cap_len_width)
type CapLen       = range(0, (2 ^ cap_len_width))
type CapPermsBits = bits(cap_perms_width)
type CapFlagsBits = bits(cap_flags_width)

/* Reset E and T calculated to make top 2**xlen. */
let cap_max_E   = cap_len_width - cap_mantissa_width + 1
let cap_reset_E = to_bits(cap_E_width, cap_max_E)
let cap_reset_T = 0b01 @ zeros(cap_mantissa_width - 2)

/*! A partially decompressed version of a capability -- E, B, T,
 * lenMSB, sealed and otype fields are not present in all formats and are
 * populated by capBitsToCapability.
 */
struct Capability = {
  tag                    : bool,
  uperms                 : bits(cap_uperms_width),
  permit_set_CID         : bool,
  access_system_regs     : bool,
  permit_unseal          : bool,
  permit_cinvoke         : bool,
  permit_seal            : bool,
  permit_store_local_cap : bool,
  permit_store_cap       : bool,
  permit_load_cap        : bool,
  permit_store           : bool,
  permit_load            : bool,
  permit_execute         : bool,
  global                 : bool,
  reserved               : bits(cap_reserved_width),
  flag_cap_mode          : bool,
  internal_E             : bool,
  E                      : bits(cap_E_width),
  B                      : bits(cap_mantissa_width),
  T                      : bits(cap_mantissa_width),
  otype                  : bits(cap_otype_width),
  address                : bits(cap_addr_width)
}

let null_cap : Capability = struct {
  tag                    = false,
  uperms                 = zeros(),
  permit_set_CID         = false,
  access_system_regs     = false,
  permit_unseal          = false,
  permit_cinvoke         = false,
  permit_seal            = false,
  permit_store_local_cap = false,
  permit_store_cap       = false,
  permit_load_cap        = false,
  permit_store           = false,
  permit_load            = false,
  permit_execute         = false,
  global                 = false,
  reserved               = zeros(),
  flag_cap_mode          = false,
  internal_E             = true,
  E                      = cap_reset_E,
  B                      = zeros(),
  T                      = cap_reset_T,
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

let default_cap : Capability = struct {
  tag                    = true,
  uperms                 = ones(),
  permit_set_CID         = true,
  access_system_regs     = true,
  permit_unseal          = true,
  permit_cinvoke         = true,
  permit_seal            = true,
  permit_store_local_cap = true,
  permit_store_cap       = true,
  permit_load_cap        = true,
  permit_store           = true,
  permit_load            = true,
  permit_execute         = true,
  global                 = true,
  reserved               = zeros(),
  flag_cap_mode          = false,
  internal_E             = true,
  E                      = cap_reset_E,
  B                      = zeros(),
  T                      = cap_reset_T,
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

function getCapHardPerms(cap) : Capability -> bits(cap_hperms_width) =
   (bool_to_bits(cap.permit_set_CID)
  @ bool_to_bits(cap.access_system_regs)
  @ bool_to_bits(cap.permit_unseal)
  @ bool_to_bits(cap.permit_cinvoke)
  @ bool_to_bits(cap.permit_seal)
  @ bool_to_bits(cap.permit_store_local_cap)
  @ bool_to_bits(cap.permit_store_cap)
  @ bool_to_bits(cap.permit_load_cap)
  @ bool_to_bits(cap.permit_store)
  @ bool_to_bits(cap.permit_load)
  @ bool_to_bits(cap.permit_execute)
  @ bool_to_bits(cap.global))

/* Convert from capability bits (128 bits with tag) to a more convenient struct. */
function encCapabilityToCapability(t,c) : (bool, EncCapability) -> Capability = {
  internal_E : bool = bit_to_bool(c.internal_E);
  E : bits(cap_E_width)  = zeros();
  Bs : bits(cap_mantissa_width) = zeros();
  T : bits(cap_mantissa_width - 2) = zeros();
  lenMSBs : bits(2) = zeros();
  if internal_E then {
    E = c.T[internal_E_take_bits - 1..0] @ c.B[internal_E_take_bits - 1..0];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    T = c.T[cap_mantissa_width - 3..3] @ zeros(internal_E_take_bits);
    Bs = c.B[cap_mantissa_width - 1..3] @ zeros(internal_E_take_bits);
  } else {
    /* Exponent zero */
    lenMSBs = 0b00;
    T = c.T;
    Bs = c.B;
  };
  /* Reconstruct top two bits of T given T = B + len and:
   * 1) the top two bits of B
   * 2) most significant two bits of length derived from format above
   * 3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
   */
  carry_out = if T <_u Bs[cap_mantissa_width - 3..0] then 0b01 else 0b00;
  Ttop2 = Bs[cap_mantissa_width - 1..cap_mantissa_width - 2] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = if cap_uperms_width > 0 then c.perms[cap_hperms_width + cap_uperms_width - 1..cap_hperms_width] else [],
    permit_set_CID         = bit_to_bool(c.perms[11]),
    access_system_regs     = bit_to_bool(c.perms[10]),
    permit_unseal          = bit_to_bool(c.perms[9]),
    permit_cinvoke         = bit_to_bool(c.perms[8]),
    permit_seal            = bit_to_bool(c.perms[7]),
    permit_store_local_cap = bit_to_bool(c.perms[6]),
    permit_store_cap       = bit_to_bool(c.perms[5]),
    permit_load_cap        = bit_to_bool(c.perms[4]),
    permit_store           = bit_to_bool(c.perms[3]),
    permit_load            = bit_to_bool(c.perms[2]),
    permit_execute         = bit_to_bool(c.perms[1]),
    global                 = bit_to_bool(c.perms[0]),
    reserved               = c.reserved,
    flag_cap_mode          = bit_to_bool(c.flags[0]),
    internal_E             = internal_E,
    E                      = E,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = c.otype,
    address                = c.address
  }
}

function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = encCapabilityToCapability(t, capBitsToEncCapability(c))

function capToEncCap(cap) : Capability -> EncCapability = {
  t_hi : bits(cap_mantissa_width - 2 - internal_E_take_bits) = cap.T[cap_mantissa_width - 3..internal_E_take_bits];
  t_lo : bits(internal_E_take_bits)  = cap.T[internal_E_take_bits - 1..0];
  b_hi : bits(cap_mantissa_width - internal_E_take_bits) = cap.B[cap_mantissa_width - 1..internal_E_take_bits];
  b_lo : bits(internal_E_take_bits)  = cap.B[internal_E_take_bits - 1..0];
  if cap.internal_E then {
    t_lo = cap.E[2 * internal_E_take_bits - 1..internal_E_take_bits];
    b_lo = cap.E[internal_E_take_bits - 1..0];
  };
  return struct {
    perms = cap.uperms @ getCapHardPerms(cap),
    reserved = cap.reserved,
    flags = bool_to_bits(cap.flag_cap_mode),
    otype = cap.otype,
    internal_E = bool_to_bits(cap.internal_E)[0],
    T = t_hi @ t_lo,
    B = b_hi @ b_lo,
    address = cap.address
  };
}

/* Convert from capability struct to bits (no tag) */
function capToBits(cap) : Capability -> CapBits = encCapToBits(capToEncCap(cap))

/* When saving/restoring capabilities xor them with bits of null_cap --
 * this ensures that canonical null_cap is always all-zeros in memory
 * even though it may have bits set logically (e.g. length or exponent
 */

let null_cap_bits : CapBits = capToBits(null_cap)

function capToMemBits(cap) : Capability -> CapBits =
  capToBits(cap) ^ null_cap_bits

function memBitsToCapability(tag, b) : (bool, CapBits) -> Capability =
  capBitsToCapability(tag, b ^ null_cap_bits)



function getCapBoundsBits(c) : Capability -> (CapAddrBits, CapLenBits) =
  let E = min(cap_max_E, unsigned(c.E)) in
  let a : CapAddrBits = c.address in
  /* Extract bits we need to make the top correction and calculate representable limit */
  let a3 = truncate(a >> (E + cap_mantissa_width - 3), 3) in
  let B3 = truncateLSB(c.B, 3) in
  let T3 = truncateLSB(c.T, 3) in
  let R3 = B3 - 0b001 in /* wraps */
  /* Do address, base and top lie in the R aligned region above the one containing R? */
  let aHi = if a3 <_u R3 then 1 else 0 in
  let bHi = if B3 <_u R3 then 1 else 0 in
  let tHi = if T3 <_u R3 then 1 else 0 in
  /* Compute region corrections for top and base relative to a */
  let correction_base = bHi - aHi in
  let correction_top  = tHi - aHi in
  let a_top = (a >> (E + cap_mantissa_width)) in {
    base : CapLenBits = truncate((a_top + correction_base) @ c.B @ zeros(E), cap_len_width);
    top  : CapLenBits = truncate((a_top + correction_top)  @ c.T @ zeros(E), cap_len_width);
    /* If the base and top are more than an address space away from each other,
       invert the MSB of top.  This corrects for errors that happen when the
       representable space wraps the address space. */
    let base2 : bits(2) = 0b0 @ [base[cap_addr_width - 1]];
    let top2  : bits(2) = top[cap_addr_width .. cap_addr_width - 1];
    if (E < (cap_max_E - 1)) & (unsigned(top2 - base2) > 1) then {
      top[cap_addr_width] = ~(top[cap_addr_width]);
    };
    /* TODO The following top MSB correction was thought to be equivalent
       to the one above, but differs at least in some cases where E >= cap_max_E - 1
    if (base[cap_addr_width] == bitone) then {
       top[cap_addr_width] = if (aHi == 1) & (tHi == 1) then bitone else bitzero;
    };
    */
    (base[(cap_addr_width - 1)..0], top)
  }

function getCapBounds(cap) : Capability -> (CapAddrInt, CapLen) =
  let (base, top) = getCapBoundsBits(cap) in
  (unsigned(base), unsigned(top))

/* An 'ideal' version of setCapBounds as described in paper. */
function setCapBounds(cap, base, top) : (Capability, CapAddrBits, CapLenBits) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  let ext_base = 0b0 @ base;
  let length = top - ext_base;
  /* Find an exponent that will put the most significant bit of length
   * second from the top as assumed during decoding. We ignore the bottom
   * MW bits because those are handled by the ie = 0 format.
   */
  let e = cap_max_E - count_leading_zeros(length[cap_addr_width..cap_mantissa_width - 1]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // but the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | length[cap_mantissa_width - 2] == bitone;

  /* The non-ie e == 0 case is easy. It is exact so just extract relevant bits. */
  Bbits = truncate(base, cap_mantissa_width);
  Tbits = truncate(top, cap_mantissa_width);
  lostSignificantTop : bool = false;
  lostSignificantBase : bool = false;
  incE : bool = false;

  if ie then {
    /* the internal exponent case is trickier */

    /* Extract B and T bits (we lose 3 bits of each to store the exponent) */
    B_ie = truncate(base >> (e + 3), cap_mantissa_width - 3);
    T_ie = truncate(top >> (e + 3), cap_mantissa_width - 3);

    /* Find out whether we have lost significant bits of base and top using a
     * mask of bits that we will lose (including 3 extra for exp).
     */
    maskLo : CapLenBits = EXTZ(ones(e+3));
    lostSignificantBase = unsigned(ext_base & maskLo) != 0;
    lostSignificantTop  = unsigned(top & maskLo) != 0;

    if lostSignificantTop then {
      /* we must increment T to make sure it is still above top even with lost bits.
         It might wrap around but if that makes B<T then decoding will compensate. */
      T_ie = T_ie + 1;
    };

    /* Has the length overflowed? We chose e so that the top two bits of len would be 0b01,
       but either because of incrementing T or losing bits of base it might have grown. */
    len_ie = T_ie - B_ie;
    if len_ie[cap_mantissa_width - 4] == bitone then {
      /* length overflow -- increment E by one and then recalculate
         T, B etc accordingly */
      incE = true;

      lostSignificantBase = lostSignificantBase | B_ie[0] == bitone;
      lostSignificantTop  = lostSignificantTop | T_ie[0] == bitone;

      B_ie = truncate(base >> (e + 4), cap_mantissa_width - 3);
      let incT : range(0,1) = if lostSignificantTop then 1 else 0;
      T_ie = truncate(top >> (e + 4), cap_mantissa_width - 3) + incT;
    };

    Bbits = B_ie @ 0b000;
    Tbits = T_ie @ 0b000;
  };
  let newCap = {cap with address=base, E=to_bits(6, if incE then e + 1 else e), B=Bbits, T=Tbits, internal_E=ie};
  let exact = not(lostSignificantBase | lostSignificantTop);
  (exact, newCap)
}

function getCapPerms(cap) : Capability -> CapPermsBits =
    let perms : bits(cap_uperms_shift) = EXTZ(getCapHardPerms(cap)) in
    cap.uperms @ perms

function setCapPerms(cap, perms) : (Capability, CapPermsBits) -> Capability =
    { cap with
      uperms                 = truncate(perms >> cap_uperms_shift, cap_uperms_width),
      /* 14..12 reserved -- ignore */
      permit_set_CID         = bit_to_bool(perms[11]),
      access_system_regs     = bit_to_bool(perms[10]),
      permit_unseal          = bit_to_bool(perms[9]),
      permit_cinvoke         = bit_to_bool(perms[8]),
      permit_seal            = bit_to_bool(perms[7]),
      permit_store_local_cap = bit_to_bool(perms[6]),
      permit_store_cap       = bit_to_bool(perms[5]),
      permit_load_cap        = bit_to_bool(perms[4]),
      permit_store           = bit_to_bool(perms[3]),
      permit_load            = bit_to_bool(perms[2]),
      permit_execute         = bit_to_bool(perms[1]),
      global                 = bit_to_bool(perms[0])
      }

/*!
 * Gets the architecture specific capability flags for given capability.
 */
val getCapFlags : Capability -> CapFlagsBits
function getCapFlags(cap) = bool_to_bits(cap.flag_cap_mode)

/*!
 * THIS`(cap, flags)` sets the architecture specific capability flags on `cap`
 * to `flags` and returns the result as new capability.
 */
val setCapFlags : (Capability, CapFlagsBits) -> Capability
function setCapFlags(cap, flags) = {cap with flag_cap_mode = bit_to_bool(flags[0])}

val isCapSealed : Capability -> bool
function isCapSealed(cap) = signed(cap.otype) != otype_unsealed

/*!
 * Tests whether the capability has a reserved otype (larger than [cap_max_otype]).
 * Note that this includes both sealed (e.g. sentry) and unsealed (all ones)
 * otypes.
 */
val hasReservedOType : Capability -> bool
function hasReservedOType(cap) = unsigned(cap.otype) > cap_max_otype

function sealCap(cap, otyp) : (Capability, bits(cap_otype_width)) -> Capability =
    {cap with otype=otyp}

function unsealCap(cap) : Capability -> Capability =
    {cap with otype=to_bits(cap_otype_width, otype_unsealed)}

function getCapBaseBits(c) : Capability -> CapAddrBits =
    let (base, _) = getCapBoundsBits(c) in
    base

function getCapBase(c) : Capability -> CapAddrInt =
    unsigned(getCapBaseBits(c))

function getCapTopBits(c) : Capability -> CapLenBits =
    let (_, top) = getCapBoundsBits(c) in
    top

function getCapTop (c) : Capability -> CapLen =
    unsigned(getCapTopBits(c))

function getCapOffsetBits(c) : Capability -> CapAddrBits =
    let base : CapAddrBits = getCapBaseBits(c) in
    c.address - base

function getCapOffset(c) : Capability -> CapAddrInt =
    unsigned(getCapOffsetBits(c))

function getCapLength(c) : Capability -> CapLen =
    let ('base, 'top) = getCapBounds(c) in {
        /* For valid capabilties we expect top >= base and hence
         * length >= 0 but representation does allow top < base in some
         * cases so might encounter on untagged capabilities. Here we just
         * pretend it is a 65-bit quantitiy and wrap.
         */
        assert (not(c.tag) | top >= base);
        (top - base) % pow2(cap_len_width)
    }

val inCapBounds  : (Capability, CapAddrBits, CapLen) -> bool
function inCapBounds (cap, addr, size) = {
  let (base, top) = getCapBounds(cap);
  let a = unsigned(addr);
  (a >= base) & ((a + size) <= top)
}

function getCapCursor(cap) : Capability -> CapAddrInt = unsigned(cap.address)

function int_to_cap (offset) : CapAddrBits -> Capability =
    {null_cap with address = offset}

function clearTagIf(cap, cond) : (Capability, bool) -> Capability =
    {cap with tag = cap.tag & not(cond)}

function clearTagIfSealed(cap) : Capability -> Capability =
    clearTagIf(cap, isCapSealed(cap))

function clearTag(cap) : Capability -> Capability =
    {cap with tag = false}

function capBoundsEqual (c1, c2) : (Capability, Capability) -> bool =
    let (base1, top1) = getCapBounds(c1) in
    let (base2, top2) = getCapBounds(c2) in
    (base1 == base2) & (top1 == top2)

val setCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function setCapAddr(c, addr) =
    let newCap = { c with address = addr } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

infix 1 >>_s
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}
overload operator >>_s = {sail_arith_shiftright}

function fastRepCheck(c, i) : (Capability, CapAddrBits) -> bool=
    let E = unsigned(c.E) in
    if (E >= cap_max_E - 2) then
        true /* in this case representable region is whole address space */
    else
        let i_top    = signed(i >>_s (E + cap_mantissa_width)) in
        let i_mid    = truncate(i >> E, cap_mantissa_width)in
        let a_mid    = truncate(c.address >> E, cap_mantissa_width) in
        let B3 = truncateLSB(c.B, 3) in
        let R3 = B3 - 0b001 in
        let R  = R3 @ zeros(cap_mantissa_width - 3) in
        let diff  = R - a_mid in
        let diff1 = diff - 1 in
        /* i_top determines 1. whether the increment is inRange
           i.e. less than the size of the representable region
           (2**(E+MW)) and 2. whether it is positive or negative. To
           satisfy 1. all top bits must be the same so we are
           interested in the cases i_top is 0 or -1 */
        if (i_top == 0) then
          i_mid <_u diff1
        else if (i_top == -1) then
          (i_mid >=_u diff) & (R != a_mid)
        else
          false

function setCapOffset(c, offset) : (Capability, CapAddrBits) -> (bool, Capability) =
    let base = getCapBaseBits(c) in
    let newAddress = base + offset in
    let newCap     = { c with address = newAddress } in
    /* let representable = capBoundsEqual(c, newCap) in */
    let representable = fastRepCheck(c, (newAddress - c.address)) in
    (representable, newCap)

function setCapOffsetChecked (cap, offset) : (Capability, CapAddrBits) -> Capability =
    let (representable, newCap) = setCapOffset(cap, offset) in
    clearTagIf(newCap, not(representable) | isCapSealed(cap))

function incCapOffset(c, delta) : (Capability, CapAddrBits) -> (bool, Capability) =
    let newAddress : CapAddrBits = c.address + delta in
    let newCap     = { c with address = newAddress } in
    /* let representable = capBoundsEqual(c, newCap) in */
    let representable = fastRepCheck(c, delta) in
    (representable, newCap)


val capToString : (Capability) -> string effect {escape}
function capToString (cap) = {
  let len = getCapLength(cap);
  let len_str = BitStr(to_bits(cap_len_width + 3, len));
  /* Print architectural type which is -1 for unsealed caps */
  let otype64 : CapAddrBits = if hasReservedOType(cap) then EXTS(cap.otype) else EXTZ(cap.otype);
  concat_str(" t:",
  concat_str(if cap.tag then "1" else "0",
  concat_str(" s:",
  concat_str(if isCapSealed(cap) then "1" else "0",
  concat_str(" perms:",
  concat_str(BitStr(0b0 @ getCapPerms(cap)),
  concat_str(" type:",
  concat_str(BitStr(otype64),
  concat_str(" offset:",
  concat_str(BitStr(getCapOffsetBits(cap)),
  concat_str(" base:",
  concat_str(BitStr(getCapBaseBits(cap)),
  concat_str(" length:", len_str)))))))))))))
}
function getRepresentableAlignmentMask(len) : xlenbits -> xlenbits = {
  let (exact, c) = setCapBounds(default_cap, to_bits(sizeof(xlen), 0), 0b0 @ len);
  let e = min(unsigned(c.E), cap_max_E);
  let e' = if c.internal_E then e + internal_E_take_bits else 0;
  ones(sizeof(xlen)-e') @ zeros(e')
}

function getRepresentableLength(len) : xlenbits -> xlenbits = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}
