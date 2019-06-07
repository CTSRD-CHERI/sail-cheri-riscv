
/* fails would be nice */
$counterexample
function propBaseLeqTop(capBits) : bits(128) -> bool = {
    let c = capBitsToCapability(true, capBits);
    let (base, top) = getCapBounds(c);
    unsigned(c.E) >= 51 | base <= top;
}

/* check that can copy bits through cap register safely  */
$counterexample
function propCapDecodeEncode(capBits) : bits(128) -> bool  = {
  let c = capBitsToCapability(true, capBits);
  let b = capToBits(c);
  b == capBits
}

/* passes
$counterexample
function propSetBounds(capBits, reqBase, reqTop) : (bits(128), bits(64), bits(65)) -> bool = {
  let c = capBitsToCapability(true, capBits);
  let (origBase, origTop) = getCapBounds(c);
  let (exact, newCap) = setCapBounds(c, reqBase, reqTop);
  // round trip through bits to check that setBounds returned encodable capability
  let newCap' = capBitsToCapability(true, capToBits(newCap));
  let (newBase, newTop) = getCapBounds(newCap');
  let reqBasei = unsigned(reqBase);
  let reqTopi = unsigned(reqTop);
  // exclude invalid initial caps
  let sensibleCap = origBase <= origTop & origTop <= pow2(64);
  // exclude invalid bounds requests
  let sensibleBounds = reqBasei <= reqTopi & reqTopi <= pow2(64);
  // exclude non-monotonic bounds requests
  let requestMonotonic = origBase <= reqBasei & reqTopi <= origTop;
  // check that returned region includes requested
  let requestSatisfied = newBase <= reqBasei & reqTopi <= newTop;
  // check that returned region does not exceed original
  let monotonic = origBase <= newBase & newTop <= origTop;
  not(sensibleCap) | not(sensibleBounds) | not(requestMonotonic) | (requestSatisfied & monotonic)
}
 */

/* passes -- trivial */
$counterexample
function prop_inc_bounds_eq(c : Capability, delta : bits(64)) -> bool = {
  let (representable, c') = incCapOffset(c, delta) in
  ~(representable) | capBoundsEqual(c, c')
}


/* passes */
$counterexample
function prop_set_bounds_exact(c : Capability, base' : bits(64), top' : bits(65)) -> bool = {
  let (exact, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  ~(exact)  | (unsigned(base') >= unsigned(top')) | (base'' == unsigned(base') & top'' == unsigned(top'))
}

/* passes
$counterexample
function prop_set_bounds_mono(cbits : bits(128), base' : bits(64), top' : bits(65)) -> bool = {
  let c = capBitsToCapability(true, cbits);
  let (base, top) = getCapBounds(c);
  let (_, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  let capSensible = base <= top;
  let requestSensible = unsigned(base') <= unsigned(top');
  let requestMonotonic = base <= unsigned(base') & unsigned(top') <= top;
  let resultMonotonic = base <= base'' & top'' <= top;
  not(capSensible) | not(requestSensible) | not(requestMonotonic) | resultMonotonic;
}
*/