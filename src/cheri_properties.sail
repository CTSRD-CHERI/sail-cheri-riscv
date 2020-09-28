/*
 * Properties of compressed capability functions
 */

$suppress_warnings

/* Syntactic sugar */

infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = not('p) | 'q
val operator --> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p --> 'q)
function operator --> (p, q) = not_bool(p) | q

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)
val operator <--> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p <--> 'q)
function operator <--> (p, q) = (p --> q) & (q --> p)

/*****************************************************************************/

/* Encodability of capabilities

   This specification uses a record type "Capability" and only converts
   to/from the in-memory bit representation when loading from/storing to
   memory.  A value of the "Capability" record is not fully decompressed
   (it still only has the mantissas of base and top instead of their
   decoded values), but it adds a few bits compared to the in-memory
   representation:

     - the two MSBs of T, inferred from the base
     - a sealed flag, derived from the object type
     - a separate exponent field (with the low bits of B and T set to zero
       if the exponent was taken from there)

   We define a notion of "encodable" Capability records, where these values
   are computed correctly, and show that this is suitably preserved by
   capability manipulation functions.  If the specification always
   used the in-memory representation, this would not be an issue.
 */

function encodableCap(c) : Capability -> bool =
  let Bbot = truncate(c.B, mantissa_width - 2) in
  let Tbot = truncate(c.T, mantissa_width - 2) in
  let Btop2 = truncateLSB(c.B, 2) in
  let Ttop2 = truncateLSB(c.T, 2) in
  let Ltop2 = if c.internal_e then 0b01 else 0b00 in
  let carry_out = if Tbot <_u Bbot then 0b01 else 0b00 in
  let top_correct = (Ttop2 == Btop2 + Ltop2 + carry_out) in
  let ie_correct = (c.internal_e | (unsigned(c.E) == 0)) in
  let Bie = truncate(c.B, internal_exponent_take_bits) in
  let Tie = truncate(c.T, internal_exponent_take_bits) in
  let Zie = zeros(internal_exponent_take_bits) in
  let bot_correct = (if c.internal_e then Bie == Zie & Tie == Zie else true) in
  let sealed_correct = (c.sealed == (c.otype != to_bits(cap_otype_width, otype_unsealed))) in
  top_correct & bot_correct & ie_correct & sealed_correct

/* A Capability is encodable iff the back-and-forth conversion to and
   from the in-memory represenation is the identity. */
$property
function propEncodableCorrect(c) : Capability -> bool =
  encodableCap(c) <--> (memBitsToCapability(c.tag, capToMemBits(c)) == c)

/* The decoding of a bit pattern is encodable */
$property
function propDecodeEncodable(capBits, tag) : (CapBits, bool) -> bool =
  encodableCap(memBitsToCapability(tag, capBits))

/* Initial and null capabilites are encodable. */
$property
function propDefaultCapEncodable() : unit -> bool = encodableCap(default_cap)

$property
function propNullCapEncodable() : unit -> bool = encodableCap(null_cap)

/* Setting bounds with a non-negative length preserves encodability. */
$property
function propSetBoundsEncodable(c, reqBase, reqTop) : (Capability, CapAddrBits, CapLenBits) -> bool =
  let (_, c') = setCapBounds(c, reqBase, reqTop) in
  let sensibleRequest = unsigned(reqBase) <= unsigned(reqTop) in
  (encodableCap(c) & sensibleRequest) --> encodableCap(c')

/* Sealing with a valid object type preserves encodability */
$property
function propSealEncodable(c, otype) : (Capability, bits(cap_otype_width)) -> bool =
  let validType = (unsigned(otype) <= max_otype) in
  (encodableCap(c) & validType) --> encodableCap(sealCap(c, otype))

/* Unsealing preserves encodability */
$property
function propUnsealEncodable(c) : Capability -> bool =
  encodableCap(c) --> encodableCap(unsealCap(c))

/* Other capability manipulations do not change the bounds, the sealed flag,
   or the object type, and therefore trivially preserve encodability. */

/*****************************************************************************/

/* The decoding of bounds normally ensures that base <= top.  However, the
   implementation currently assumes that, in case of high exponents, the most
   significant bits of B/T that would end up above 64/65 bits are zero.  We
   show that setCapBounds does not generate capabilities that violate this,
   if the requested top is at or below 2^64, which is the top of the initial
   capability.  Hence, for any (encodable) capability ultimately derived from
   the initial capability in a monotonic way, base <= top should hold. */

function validBounds(c) : Capability -> bool =
  let Bmsb  = c.B[mantissa_width - 1] in
  let Bmsb2 = c.B[mantissa_width - 1 .. mantissa_width - 2] in
  let Tmsb  = c.T[mantissa_width - 1] in
  if (unsigned(c.E) > maxE) then {
    false
  } else if (unsigned(c.E) == maxE) then {
    Tmsb == bitzero & Bmsb2 == 0b00
  } else if (unsigned(c.E) == maxE - 1) then {
    Bmsb == bitzero
  } else true

$property
function propSetBoundsValid(c, reqBase, reqTop) : (Capability, CapAddrBits, CapLenBits) -> bool =
  let (_, c') = setCapBounds(c, reqBase, reqTop) in
  let sensibleReq = unsigned(reqTop) <= pow2(cap_addr_width) in
  sensibleReq --> validBounds(c')

$property
function propBaseLeqTop(c) : Capability -> bool =
  let (base, top) = getCapBounds(c) in
  (encodableCap(c) & validBounds(c)) --> (base <= top)

$property
function propBuildCapValidEq(c, auth) : (Capability, Capability) -> bool =
  let (base, top) = getCapBoundsBits(c) in
  let (_, c1) = setCapBounds(auth, base, top) in
  let (_, c2) = setCapOffset(c1, getCapOffsetBits(c)) in
  let c3 = setCapPerms(c2, getCapPerms(c)) in
  let result = setCapFlags(c3, getCapFlags(c)) in
  let expected_result = {unsealCap(c) with tag = true, reserved = auth.reserved} in
  (encodableCap(c) & encodableCap(auth) & validBounds(c) & auth.tag & not(auth.sealed)) --> (result == expected_result)

/*****************************************************************************/

/* Monotonicity of setCapBounds, under preconditions corresponding to the
   checks performed by the CSetBounds instructions (and assuming reachable
   capabilities, in particular with top <= 2^64). */
$property
function propSetBounds(c, reqBase, reqTop) : (Capability, CapAddrBits, CapLenBits) -> bool = {
  let (origBase, origTop) = getCapBounds(c);
  let (exact, newCap) = setCapBounds(c, reqBase, reqTop);
  let (newBase, newTop) = getCapBounds(newCap);
  let reqBasei = unsigned(reqBase);
  let reqTopi = unsigned(reqTop);
  // exclude invalid bounds requests
  let requestSensible = reqBasei <= reqTopi & reqTopi <= pow2(cap_addr_width);
  // exclude non-monotonic bounds requests
  let requestMonotonic = origBase <= reqBasei & reqTopi <= origTop;
  // check that returned region includes requested
  let requestSatisfied = newBase <= reqBasei & reqTopi <= newTop;
  // check that returned region does not exceed original
  let boundsMonotonic = origBase <= newBase & newTop <= origTop;
  // check that exponent does not increase
  let expMonotonic = unsigned(newCap.E) <= unsigned(c.E);
  // check that exact is true iff the returned bounds are exactly as requested
  let exactCorrect = ((reqBasei == newBase) & (reqTopi == newTop)) == exact;
  (encodableCap(c) & validBounds(c) & requestSensible & requestMonotonic)
  --> (requestSatisfied & boundsMonotonic & expMonotonic & exactCorrect)
}

/* set/incCapOffset do not change the bounds of capabilities, if the
   representability check succeeds. */
$property
function propSetOffset(c, offset) : (Capability, CapAddrBits) -> bool = {
  let (origBase, origTop) = getCapBounds(c);
  let (representable, c') = setCapOffset(c, offset);
  let (newBase, newTop) = getCapBounds(c');
  representable --> (newBase == origBase & newTop == origTop)
}

$property
function propIncOffset(c, offset) : (Capability, CapAddrBits) -> bool = {
  let (origBase, origTop) = getCapBounds(c);
  let (representable, c') = incCapOffset(c, offset);
  let (newBase, newTop) = getCapBounds(c');
  representable --> (newBase == origBase & newTop == origTop)
}

/* TODO: Elaborate on the representable range, as in this earlier attempt: */
/*
$counterexample
function propSetOffset(base, top, offset) : (CapAddrBits, CapLenBits, CapAddrBits) -> bool = {
  let (exact, cap) = setCapBounds(default_cap, base, top);
  let (representable, cap') = setCapOffset(cap, offset);
  let (origBase, origTop) = getCapBounds(cap);
  let (newBase, newTop)   = getCapBounds(cap');
  let sensibleCap = ((0b0 @ base) <=_u top) & (unsigned(top) <= pow2(cap_addr_width));
  let len = max(pow2(mantissa_width - 2), origTop - origBase);
  let lowerRepOff = 0 - len;
  let upperRepOff = 6 * len;
  let signedOff = 4 * signed(offset);
  let inRepBounds = (lowerRepOff < signedOff) & (signedOff < upperRepOff);
  let representableCorrect = ((origBase == newBase) & (origTop == newTop)) == representable;
  not(sensibleCap) | (representableCorrect & (inRepBounds == representable))
}
*/
