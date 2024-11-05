/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// Width of capability in bytes (excluding tag).
// TODO: Rename to clen_bytes and clen?
// TODO: Change root xlen to be in terms of the log2 bytes.
type cap_size : Int = xlen_bytes * 2
let  cap_size = sizeof(cap_size)

type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
type cap_len_width : Int = cap_addr_width + 1
let  cap_len_width = sizeof(cap_len_width)

let cap_max_addr = MAX(cap_addr_width)

// 64 or 128 bits.
type CapBits = bits(8 * cap_size)

// XLEN (32 or 64).
type CapAddrBits  = bits(cap_addr_width)
type CapAddrInt   = range(0, (2 ^ cap_addr_width) - 1)

// XLEN+1 (33 or 65).
type CapLenBits   = bits(cap_len_width)
type CapLenInt    = range(0, (2 ^ cap_len_width) - 1)

// Width of TE and BE fields.
type cap_xe_width : Int = div(cap_E_width, 2)
let  cap_xe_width = sizeof(cap_xe_width)

// Maximum exponent (24 or 52).
// The final exponent is calculated by subtracting a 5 or 6 bit value from
// this, giving a range of 24 .. 0, or 52 .. 0. If the exponent becomes
// negative then it is ignored.
type cap_max_E : Int = cap_addr_width - cap_mantissa_width + 2
let  cap_max_E = sizeof(cap_max_E)

// Negative exponents can be encoded, though these are malformed. We must
// store all of the possible values (even malformed ones) so that CSetHigh works.
type cap_min_E : Int = cap_max_E - (2 ^ cap_E_width - 1)
let  cap_min_E = sizeof(cap_min_E)

type CapExponent = range(cap_min_E, cap_max_E)

// Encoding of the EF bit to whether or not it's an internal exponent.
mapping internal_exponent_encdec : bool <-> bits(1) = {
  // Exponent is zero.
  false <-> 0b1,
  // Exponent is internal (stored in L8, TE, BE).
  true <-> 0b0,
}

// A partially decompressed version of a capability. Note that this is a
// losslessly decompressed version. All of the original metadata bits are
// preserved, including reserved ones. This is necessary so that CSetHigh works.
struct Capability = {
  // Is the cap valid.
  tag               : bool,
  // Software defined permission bits.
  sd_perms          : bits(cap_sd_perms_width),
  // Compressed architectural permissions and mode
  ap_m              : bits(cap_AP_M_width),
  // Is the cap sealed.
  sealed            : bool,
  // Whether the exponent is zero or internal in the top/bottom fields.
  // This only depends on E and the cap bounds, so it is technically redundant
  // here, but it is more efficient to keep a copy. It is update by
  // setCapBounds().
  internal_exponent : bool,
  // Exponent
  E                 : CapExponent,
  // Bottom
  B                 : bits(cap_mantissa_width),
  // Top
  T                 : bits(cap_mantissa_width),
  // Reserved bits. These are preserved.
  reserved_0        : bits(cap_reserved_0_width),
  reserved_1        : bits(cap_reserved_1_width),
  // Non-CHERI bits.
  address           : bits(cap_addr_width),
}

// Decode compressed capability to a more convenient struct.
function bitsToCap(tag : bool, cap_bits : CapBits) -> Capability = {
  // Decode metadata to fields.
  let meta = Mk_EncMetadata(cap_bits[xlen * 2 - 1 .. xlen]);

  let internal_exponent = internal_exponent_encdec(meta[EF]);

  // For brevity and to match the spec.
  let 'MW = cap_mantissa_width;

  let E : CapExponent = if internal_exponent then cap_max_E - unsigned(getMetadataInternalExponent(meta)) else 0;

  // When the exponent is non-zero (internal_exponent is true) we implicitly
  // store the leading 1, just as with normal floating point numbers.
  // The case when the exponent is zero is equivalent to subnormals.
  let LMSB = if internal_exponent then 0b01 else 0b0 @ getMetadataL8(meta);

  // `not()` so type infererence for zeros() works.
  let T_low = if not(internal_exponent) then meta[TE] else zeros();
  let B_low = if not(internal_exponent) then meta[BE] else zeros();

  // Concatenate all the bits. Type annotations are not require but here for sanity checking.
  let T : bits('MW - 2) = meta[Tm] @ T_low;
  let B : bits('MW)     = meta[Bm] @ B_low;

  let LCout = if T <_u B[MW - 3 .. 0] then 0b01 else 0b00;

  // Prepend the reconstructed top two bits of T.
  let T = (B[MW - 1 .. MW - 2] + LCout + LMSB) @ T;

  struct {
    tag               = tag,
    sd_perms          = meta[SDP],
    ap_m              = meta[AP_M],
    sealed            = bool_bits(meta[CT]),
    internal_exponent = internal_exponent,
    E                 = E,
    B                 = B,
    T                 = T,
    reserved_0        = meta[reserved_0],
    reserved_1        = meta[reserved_1],
    address           = cap_bits[xlen - 1 .. 0],
  }
}

// Encode a capability to compressed form. Only the metadata is returned since
// the tag and address are directly available in `cap`.
function capToMetadataBits(cap : Capability) -> EncMetadata = {
  // Convert the exponent back to encoded form.
  let E = to_bits(cap_E_width, cap_max_E - cap.E);

  // The L8 value here is ignored on RV64.
  let (L8, TE, BE) = if cap.internal_exponent then {
    (
      E[cap_E_width - 1],
      E[cap_xe_width * 2 - 1 .. cap_xe_width],
      E[cap_xe_width - 1 .. 0]
    )
  } else {
    (
      (cap.T - cap.B)[8],
      cap.T[cap_xe_width - 1 .. 0],
      cap.B[cap_xe_width - 1 .. 0]
    )
  };

  let MW = cap_mantissa_width;

  let meta = [
    Mk_EncMetadata(zeros()) with
    SDP = cap.sd_perms,
    AP_M = cap.ap_m,
    CT = bool_bits(cap.sealed),
    EF = internal_exponent_encdec(cap.internal_exponent),
    Tm = cap.T[MW - 3 .. cap_xe_width],
    Bm = cap.B[MW - 1 .. cap_xe_width],
    TE = TE,
    BE = BE,
    reserved_1 = cap.reserved_1,
    reserved_0 = cap.reserved_0
  ];
  // Set L8 on RV32. Does nothing on RV64.
  setMetadataL8(meta, [L8])
}

// Zero permission capability.
// TODO: We should be able to use bitsToCap(false, zeros()) but there
// seems to be a bug: https://github.com/rems-project/sail/issues/424
let null_cap : Capability = struct {
  tag               = false,
  sd_perms          = zeros(),
  ap_m              = null_ap_m,
  sealed            = false,
  internal_exponent = true, // Encodes to 0.
  E                 = cap_max_E, // Encodes to 0.
  B                 = zeros(),
  T                 = 0b01 @ zeros(cap_mantissa_width - 2), // Encodes to 0.
  reserved_0        = zeros(),
  reserved_1        = zeros(),
  address           = zeros(),
}

// Full permission capability.
let infinite_cap : Capability = {
  null_cap with
  tag      = true,
  sd_perms = ones(),
  ap_m     = infinite_ap_m,
}

// A capability is malformed if its encoding does not describe a valid capability
// because its bounds cannot be correctly decoded.
function boundsMalformed(cap : Capability) -> bool = {
  cap.internal_exponent & ({
    let MW = cap_mantissa_width;

    let malformedMSB = (cap.E == cap_max_E     & cap.B         != zeros(MW)) |
                       (cap.E == cap_max_E - 1 & cap.B[MW - 1] != bitzero);
    let malformedLSB = cap.E < 0 | (cap_use_L8 & cap.E == 0);
    malformedMSB | malformedLSB
  })
}

// Get the full cap bounds (base and top) as bit vectors.
function getCapBoundsBits(c : Capability) -> option((CapAddrBits, CapLenBits)) = {
  if boundsMalformed(c) then return None();
  let E = c.E;
  assert(E >= 0, "Cap is malformed if E<0");

  let a = c.address;
  /* Extract bits we need to make the top correction and calculate representable limit */
  let a_mid = truncate(a >> E, cap_mantissa_width);
  let R = c.B - (0b01 @ zeros(cap_mantissa_width - 2)); /* wraps */
  /* Do address, base and top lie in the R aligned region above the one containing R? */
  let aHi = if a_mid <_u R then 1 else 0;
  let bHi = if c.B   <_u R then 1 else 0;
  let tHi = if c.T   <_u R then 1 else 0;
  /* Compute region corrections for top and base relative to a */
  let correction_base = bHi - aHi;
  let correction_top  = tHi - aHi;
  let a_top = (a >> (E + cap_mantissa_width));
  let base : CapLenBits = truncate((a_top + correction_base) @ c.B @ zeros(E), cap_len_width);
  var top  : CapLenBits = truncate((a_top + correction_top)  @ c.T @ zeros(E), cap_len_width);
  /* If the base and top are more than an address space away from each other,
      invert the MSB of top.  This corrects for errors that happen when the
      representable space wraps the address space. */
  let base2 : bits(2) = 0b0 @ [base[cap_addr_width - 1]];
  let top2  : bits(2) = top[cap_addr_width .. cap_addr_width - 1];
  if (E < (cap_max_E - 1)) & (top2 - base2 >_u 0b01) then {
    top[cap_addr_width] = ~(top[cap_addr_width]);
  };
  /* TODO The following top MSB correction was thought to be equivalent
      to the one above, but differs at least in some cases where E >= cap_max_E - 1
  if (base[cap_addr_width] == bitone) then {
      top[cap_addr_width] = if (aHi == 1) & (tHi == 1) then bitone else bitzero;
  };
  */
  let base = base[(cap_addr_width - 1) .. 0];
  Some(base, top)
}

// Utility to get the cap bounds (base and top) as integers.
function getCapBounds(cap : Capability) -> option((CapAddrInt, CapLenInt)) =
  match getCapBoundsBits(cap) {
    None()          => None(),
    Some(base, top) => Some(unsigned(base), unsigned(top))
  }

/* An 'ideal' version of setCapBounds as described in paper. */
function setCapBounds(cap : Capability, base : CapAddrBits, top : CapLenBits) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  let ext_base = 0b0 @ base;
  let length = top - ext_base;
  /* Find an exponent that will put the most significant bit of length
   * second from the top as assumed during decoding. We ignore the bottom
   * MW bits because those are handled by the ie = 0 format.
   */
  let e = cap_max_E - count_leading_zeros(length[cap_addr_width..cap_mantissa_width - 1]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | (not(cap_use_L8) & length[cap_mantissa_width - 2] == bitone);

  /* The non-ie e == 0 case is easy. It is exact so just extract relevant bits. */
  var Bbits = truncate(base, cap_mantissa_width);
  var Tbits = truncate(top, cap_mantissa_width);
  var lostSignificantTop : bool = false;
  var lostSignificantBase : bool = false;
  var incE : bool = false;

  if ie then {
    /* the internal exponent case is trickier */

    /* Extract B and T bits (we lose 2 or 3 bits of each to store the exponent) */
    var B_ie = truncate(base >> (e + cap_xe_width), cap_mantissa_width - cap_xe_width);
    var T_ie = truncate(top >> (e + cap_xe_width), cap_mantissa_width - cap_xe_width);

    /* Find out whether we have lost significant bits of base and top using a
     * mask of bits that we will lose (including 2 or 3 extra for exp).
     */
    let maskLo : CapLenBits = zero_extend(ones(e + cap_xe_width));
    lostSignificantBase = (ext_base & maskLo) != zeros();
    lostSignificantTop  = (top & maskLo) != zeros();

    if lostSignificantTop then {
      /* we must increment T to make sure it is still above top even with lost bits.
         It might wrap around but if that makes B<T then decoding will compensate. */
      T_ie = T_ie + 1;
    };

    /* Has the length overflowed? We chose e so that the top two bits of len would be 0b01,
       but either because of incrementing T or losing bits of base it might have grown. */
    let len_ie = T_ie - B_ie;
    if len_ie[cap_mantissa_width - (cap_xe_width + 1)] == bitone then {
      /* length overflow -- increment E by one and then recalculate
         T, B etc accordingly */
      incE = true;

      lostSignificantBase = lostSignificantBase | B_ie[0] == bitone;
      lostSignificantTop  = lostSignificantTop  | T_ie[0] == bitone;

      B_ie = truncate(base >> (e + cap_xe_width + 1), cap_mantissa_width - cap_xe_width);
      let incT : range(0,1) = if lostSignificantTop then 1 else 0;
      T_ie = truncate(top >> (e + cap_xe_width + 1), cap_mantissa_width - cap_xe_width) + incT;
    };

    Bbits = B_ie @ zeros(cap_xe_width);
    Tbits = T_ie @ zeros(cap_xe_width);
  };

  let newCap = {
    cap with
    address=base,
    E=if incE then {
      // TODO: E can overflow here. The previous code silently wrapped so I've
      // copied that but I'm not sure it's correct.
      //
      // An example is: address:0 base:0 top:0b10000000000000000000000000000000000000000000000000000000000000000 length:0x10000000000000000
      //                new_base:0 new_top:0b01111111111111111111111111111111111011001110000000000000000000000
      //
      if e + 1 <= cap_max_E then e + 1 else cap_min_E
    } else e,
    B=Bbits,
    T=Tbits,
    internal_exponent=ie
  };
  let exact = not(lostSignificantBase | lostSignificantTop);
  (exact, newCap)
}

function capIsSealed(cap : Capability) -> bool = cap.sealed

function sealCap(cap : Capability) -> Capability =
  {cap with sealed=true}

function unsealCap(cap : Capability) -> Capability =
  {cap with sealed=false}

// A capability is malformed if it has a reserved permission encoding.
function permsMalformed(cap : Capability) -> bool =
  not(ap_m_encdec_forwards_matches(cap.ap_m))

// Utility field functions.

function getCapPermsAndMode(cap : Capability) -> option((ArchPerms, ExecutionMode)) =
  if permsMalformed(cap) then None() else Some(ap_m_encdec(cap.ap_m))

function setCapPermsAndMode(cap : Capability, (perms, mode): (ArchPerms, ExecutionMode)) -> Capability =
  {cap with ap_m = ap_m_encdec(legalizePermsAndMode(perms, mode))}

function getArchPerms(cap : Capability) -> option(ArchPerms) =
  match getCapPermsAndMode(cap) {
    None() => None(),
    Some(perms, _) => Some(perms)
  }

function getArchPermsLegalized(cap : Capability) -> ArchPerms =
  match getArchPerms(cap) {
    None() => null_perms,
    Some(perms) => perms
  }

// Extract capability mode bit, legalising to integer pointer mode if decoding goes wrong
function getCapMode(cap : Capability) -> ExecutionMode =
  match getCapPermsAndMode(cap) {
    None() => execution_mode_encdec(0b0),
    Some(_, mode) => mode,
  }

function setArchPerms(cap : Capability, perms : ArchPerms) -> Capability =
  setCapPermsAndMode(cap, (perms, getCapMode(cap)))

function setCapMode(cap : Capability, mode : ExecutionMode) -> Capability =
  setCapPermsAndMode(cap, (getArchPermsLegalized(cap), mode))

function canASR(cap : Capability) -> bool = getArchPermsLegalized(cap).ASR
function canX(cap : Capability) -> bool = getArchPermsLegalized(cap).X
function canR(cap : Capability) -> bool = getArchPermsLegalized(cap).R
function canW(cap : Capability) -> bool = getArchPermsLegalized(cap).W
function canC(cap : Capability) -> bool = getArchPermsLegalized(cap).C
function canLM(cap : Capability) -> bool = getArchPermsLegalized(cap).LM

// Format used by GCPERM and ACPERM.
bitfield BitPerms : xlenbits = {
  reserved_2  : xlen - 1                   .. 19,
  R           : 18,
  X           : 17,
  ASR         : 16,
  reserved_1  : 15                         .. 6 + cap_sd_perms_width,
  SDP         : 6 + cap_sd_perms_width - 1 .. 6,
  C           : 5,
  reserved_0  : 4 .. 2,
  LM          : 1,
  W           : 0,
}

// Convert the capability permissions into the format expected by GCPerm and ACPerm.
function packPerms(arch_perms : ArchPerms, sd_perms : bits(cap_sd_perms_width)) -> BitPerms =
  [
    Mk_BitPerms(zeros()) with
    SDP = sd_perms,
    ASR = bool_bits(arch_perms.ASR),
    X = bool_bits(arch_perms.X),
    R = bool_bits(arch_perms.R),
    W = bool_bits(arch_perms.W),
    C = bool_bits(arch_perms.C),
    LM = bool_bits(arch_perms.LM),
  ]

function unpackPerms(perms : BitPerms) -> (ArchPerms, bits(cap_sd_perms_width)) = {
  let arch_perms : ArchPerms =
    struct {
      ASR = bool_bits(perms[ASR]),
      X = bool_bits(perms[X]),
      R = bool_bits(perms[R]),
      W = bool_bits(perms[W]),
      C = bool_bits(perms[C]),
      LM = bool_bits(perms[LM]),
    };
  (arch_perms, perms[SDP])
}

function getCapLength(c : Capability) -> CapLenInt =
  match getCapBounds(c) {
    None() => 0,
    Some(base, top) => {assert(top >= base); top - base},
  }

// Return true if the given decoded bounds cover the entire address space.
// Microarchitecturally, this should be the same as checking if the exponent
// is max_exp.
function decodedBoundsInfinite(base : CapAddrInt, top : CapLenInt) -> bool =
  (base == 0) & (top >= 2 ^ xlen)

// Return true if the given capability has infinite bounds, meaning
// it can access any byte of the address space.
function capBoundsInfinite(c: Capability) -> bool =
  match getCapBounds(c) {
    None() => false,
    Some(base, top) => decodedBoundsInfinite(base, top),
  }

// Return true if the range [addr, addr+size) is in the cap bounds.
// The upper bound arithmetic is allowed to overflow, wrapping the address space.
// `top` can be >= 2^xlen, in which case the entire address space is in bounds
// provided `base == 0`. RISC-V allows accesses to wrap, so for example if
// `addr` is 2^xlen - 2 and `size` is 4 then it will access the two highest
// bytes and the two lowest bytes. The only situation in which a wrapped
// access is in bounds is if the highest and lowest bytes are in bounds of the
// unwrapped capability bounds, and that can only happen if `base` is 0 and
// `top` is >=2^xlen (in which case every access is in bounds so we don't need
// to check `addr` or `size` at all.
function inCapBounds(cap : Capability, addr : CapAddrBits, size : CapLenInt) -> bool = {
  let a = unsigned(addr);
  match getCapBounds(cap) {
    None() => false,
    Some(base, top) => ((a >= base) & ((a + size) <= top)) | decodedBoundsInfinite(base, top)
  }
}

// Return true if any byte of the access is within the cap bounds
// Used for certain CBO instructions
function anyByteInCapBounds(cap : Capability, addr : CapAddrBits, size : CapLenInt) -> bool = {
  let a = unsigned(addr);
  match getCapBounds(cap) {
    None() => false,
    Some(base, top) => ((a < top) & ((a + size) > base)) | decodedBoundsInfinite(base, top)
  }
}

// Return true if the range [addr, addr+size) is in the cap bounds.
// The upper bound arithmetic is full-width and isn't wrapped.
function inCapBoundsNoWrap(cap : Capability, addr : CapAddrBits, size : CapLenInt) -> bool = {
  let a = unsigned(addr);
  match getCapBounds(cap) {
    None() => false,
    Some(base, top) => (a >= base) & ((a + size) <= top),
  }
}

function capReservedValid(cap : Capability) -> bool =
  (cap.reserved_0 == zeros()) & (cap.reserved_1 == zeros())

function capTaggedAndReservedValid(cap : Capability) -> bool =
  cap.tag & capReservedValid(cap)

// Return true if c0's bounds and permissions are a subset of c1's.
function capIsSubset(c0 : Capability, c1 : Capability) -> bool = {
  let bounds_subset : bool = match (getCapBounds(c0), getCapBounds(c1)) {
    (None(), _) => false,
    (_, None()) => false,
    (Some(c0_base, c0_top), Some(c1_base, c1_top)) =>
      (c0_base >= c1_base) & (c0_top <= c1_top)
  };
  let perms_subset : bool = match (getArchPerms(c0), getArchPerms(c1)) {
      (None(), _) => false,
      (_, None()) => false,
      (Some(c0_arch_perms), Some(c1_arch_perms)) => {
        let c0_perms_packed = packPerms(c0_arch_perms, c0.sd_perms).bits;
        let c1_perms_packed = packPerms(c1_arch_perms, c1.sd_perms).bits;
        (c0_perms_packed & c1_perms_packed) == c0_perms_packed;
      }
  };
  // Not a subset if reserved bits are set in either cap
  let reserved_valid = capReservedValid(c0) & capReservedValid(c1);
  bounds_subset & perms_subset & reserved_valid;
}

function clearTagIf(cap : Capability, cond : bool) -> Capability =
  {cap with tag = cap.tag & not(cond)}

function clearTag(cap : Capability) -> Capability =
  {cap with tag = false}

// Implementations are allowed to retain invalid capability permissions loaded from memory
// instead of following the ACPERM behaviour of reducing them to no permissions.
let sys_legalize_malformed_permission_on_load = false

function legalizeLM(loaded_cap : Capability, auth_cap : Capability) -> Capability = {
  // When loading a capability, if the authorizing capability does not grant LM-perm
  // and the loaded cap has tag set and isn't sealed then clear W-perm and LM-perm,
  // otherwise return the cap data unmodified. Implementations are allowed to legalize
  // malformed permissions or retain them.
  let legalize = loaded_cap.tag &
                 not(capIsSealed(loaded_cap)) &
                 not(canLM(auth_cap)) &
                 (sys_legalize_malformed_permission_on_load | not(permsMalformed(loaded_cap)));
  if not(legalize) then return loaded_cap;
  let new_perms = { getArchPermsLegalized(loaded_cap) with LM = false, W = false };
  setArchPerms(loaded_cap, new_perms)
}

function capBoundsEqual (c1 : Capability, c2 : Capability) -> bool =
  match (getCapBounds(c1), getCapBounds(c2)) {
    (None(), _) => false,
    (_, None()) => false,
    (Some(base1, top1), Some(base2, top2)) => (base1 == base2) & (top1 == top2)
  }

function setCapAddr(c : Capability, addr : CapAddrBits) -> (bool, Capability) = {
  let newCap = { c with address = addr };
  // capBoundsEqual returns false if either input has malformed bounds, so the
  // representability check will fail if the old or new bounds were malformed.
  let representable = capBoundsEqual(c, newCap);
  (representable, newCap)
}

function setCapAddrChecked(c : Capability, addr : CapAddrBits) -> Capability = {
  let (representable, newCap) = setCapAddr(c, addr);
  clearTagIf(newCap, not(representable) | capIsSealed(c) | not(capReservedValid(c)))
}

infix 1 >>_s
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}
overload operator >>_s = {sail_arith_shiftright}

function incCapAddrChecked(c : Capability, delta : CapAddrBits) -> Capability =
  setCapAddrChecked(c, c.address + delta)

function capToString(cap : Capability) -> string = {
  let (base_str, top_str, bounds_malformed) : (string, string, bool) = match getCapBoundsBits(cap) {
    None() => ("0 (malformed)", "0 (malformed)", true),
    Some(base, top) => (bits_str(base), bits_str(zero_extend(cap_len_width + 3, top)), false)
  };

  let len_str = bits_str(to_bits(cap_len_width + 3, getCapLength(cap)));

  let (arch_perms_str, perms_malformed) : (string, bool) = match getArchPerms(cap) {
    None() => ("(malformed)", true),
    Some(perms) => (
      (if perms.R then "R" else "") ^
      (if perms.W then "W" else "") ^
      (if perms.C then "C" else "") ^
      (if perms.X then "X" else "") ^
      (if perms.LM then "Lm" else "") ^
      (if perms.ASR then "Asr" else ""),
      false
    )
  };

  // Warn if non-zero reserved bits encountered
  let (res_str, reserved_malformed) : (string, bool) = if not(capReservedValid(cap)) then
    (" (has non-zero reserved bits)", true)
  else
    ("", false);

  // Print the raw metadata bits if they didn't decode to help debugging
  let raw_str = if bounds_malformed | perms_malformed | reserved_malformed then
    " raw:" ^ bits_str(capToMetadataBits(cap).bits)
  else
    "";

  let cheri_mode : string = match getCapMode(cap) {
    CapPtrMode => "CapPtrMode",
    IntPtrMode  => "Integer",
  };

  "t:" ^ (if cap.tag then "1" else "0") ^
  " address:" ^ bits_str(cap.address) ^
  " base:" ^ base_str ^
  " top:" ^ top_str ^
  " length:" ^ len_str ^
  " sealed:" ^ (if cap.sealed then "1" else "0") ^
  " perms:" ^ arch_perms_str ^
  " sdperms:" ^ bits_str(cap.sd_perms) ^
  " mode:" ^ cheri_mode ^
  raw_str ^ res_str
}

function getRepresentableAlignmentMask(len : xlenbits) -> xlenbits = {
  let (_exact, c) = setCapBounds(infinite_cap, zeros(), 0b0 @ len);
  if c.internal_exponent then {
    // setCapBounds will never make a malformed cap with E < 0.
    let e = c.E;
    assert(e >= 0);
    ~(zero_extend(ones(e + cap_xe_width)))
  } else ones()
}

function getRepresentableLength(len : xlenbits) -> xlenbits = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}
