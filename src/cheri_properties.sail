$suppress_warnings

/* fails would be nice */
$counterexample
function propBaseLeqTop(capBits) : CapBits -> bool = {
    let c = capBitsToCapability(true, capBits);
    let (base, top) = getCapBounds(c);
    unsigned(c.E) >= (maxE - 1) | base <= top;
}

/* check that can copy bits through cap register safely 
$counterexample
function propCapDecodeEncode(capBits) : CapBits -> bool  = {
  let c = capBitsToCapability(true, capBits);
  let b = capToBits(c);
  b == capBits
}
*/

/* passes  
$counterexample
function propSetBounds(capBits, reqBase, reqTop) : (CapBits, CapAddrBits, CapLenBits) -> bool = {
  let c = capBitsToCapability(true, capBits);
  let (origBase, origTop) = getCapBounds(c);
  let (exact, newCap) = setCapBounds(c, reqBase, reqTop);
  // round trip through bits to check that setBounds returned encodable capability
  let newCap' = capBitsToCapability(true, capToBits(newCap));
  let (newBase, newTop) = getCapBounds(newCap');
  let reqBasei = unsigned(reqBase);
  let reqTopi = unsigned(reqTop);
  // exclude invalid initial caps
  let sensibleCap = origBase <= origTop & origTop <= pow2(cap_addr_width);
  // exclude invalid bounds requests
  let sensibleBounds = reqBasei <= reqTopi & reqTopi <= pow2(cap_addr_width);
  // exclude non-monotonic bounds requests
  let requestMonotonic = origBase <= reqBasei & reqTopi <= origTop;
  // check that returned region includes requested
  let requestSatisfied = newBase <= reqBasei & reqTopi <= newTop;
  // check that returned region does not exceed original
  let monotonic = origBase <= newBase & newTop <= origTop;
  // check that exact is true iff the returned bounds are exactly as requested
  let exactCorrect = ((reqBasei == newBase) & (reqTopi == newTop)) == exact;
  not(sensibleCap) | not(sensibleBounds) | not(requestMonotonic) | (requestSatisfied & monotonic & exactCorrect) 
}


let test_setOffset (bounds, offset) =
  (* pair each bit list with Big_int for easy comparison etc. *)
  let zippedBounds = List.combine bounds (List.map Sail_lib.uint bounds) in
  let sortedBounds = List.sort (fun (_, a) (_, b) -> BI.compare a b) zippedBounds in
  let [base; top] = sortedBounds in
  let (exact, cap1) = Cheri_cc.zsetCapBounds(Cheri_cc.zdefault_cap, fst(base), B0::fst(top)) in
  let (rep, cap2) = Cheri_cc.zsetCapOffset(cap1, offset) in
  let zoff = Sail_lib.sint(offset) in
  let len = BI.max (BI.of_int 4096) (Cheri_cc.zgetCapLength cap1) in
  let z4 = BI.of_int 4 in
  let z6 = BI.of_int 6 in
  let lowerRepOff = BI.negate (BI.div len z4) in
  let upperRepOff = BI.div (BI.mul len z6) z4 in
  let success = rep || (BI.less zoff lowerRepOff) || (BI.greater zoff upperRepOff) in begin
      if not success then begin
          print_endline (Cheri_cc.string_of_zCapability cap1);
          print_endline ("lowerRepOff=" ^ (Z.format "x" lowerRepOff));
          print_endline ("uppperRepOff=" ^ (Z.format "x" upperRepOff));
        end;
      success
  end
*/

$counterexample
function propSetOffset(cap, offset) : (CapBits, CapAddrBits) -> bool = {
  let cap = capBitsToCapability(true, cap);
  let (representable, cap') = setCapOffset(cap, offset);
  let (origBase, origTop) = getCapBounds(cap);
  let (newBase, newTop)   = getCapBounds(cap');
  let sensibleCap = (origBase <= origTop) & (origTop <= pow2(cap_addr_width));
  let len = max(pow2(mantissa_width - 2), origTop - origBase);
  let lowerRepOff = 0 - len;
  let upperRepOff = 6 * len;
  let signedOff = 4 * signed(offset);
  let inRepBounds = (lowerRepOff < signedOff) & (signedOff < upperRepOff);
  let representableCorrect = ((origBase == newBase) & (origTop == newTop)) == representable;
  representableCorrect & (inRepBounds == representable)
}



/* passes -- trivial 
$counterexample
function prop_inc_bounds_eq(c : Capability, delta : CapAddrBits) -> bool = {
  let (representable, c') = incCapOffset(c, delta) in
  ~(representable) | capBoundsEqual(c, c')
}
*/

/* passes 
$counterexample
function prop_set_bounds_exact(c : Capability, base' : CapAddrBits, top' : CapLenBits) -> bool = {
  let (exact, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  ~(exact)  | (unsigned(base') >= unsigned(top')) | (base'' == unsigned(base') & top'' == unsigned(top'))
}
*/

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