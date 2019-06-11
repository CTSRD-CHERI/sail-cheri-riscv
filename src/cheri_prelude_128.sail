/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Robert M. Norton                              */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

/* width of capability in bytes (excluding tag) */
let 'cap_size = 16
let log2_cap_size = 4
type CapBits = bits(8*'cap_size)
/* width of otype field in bits */
let otype_width = 18
let uperms_width = 4
type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
type cap_len_width : Int = cap_addr_width + 1
let  cap_len_width  = sizeof(cap_len_width)
type mantissa_width : Int = 14
let  mantissa_width = sizeof(mantissa_width)

let MAX_ADDR = MAX(cap_addr_width)
type CapAddrInt = range(0, (2 ^ 64) - 1) /* XXX should be cap_addr_width */
type CapLen = range(0, 2 ^ 65) /* XXX sail can't handle if this is expressed as cap_len_width */

/* A partially decompressed version of a capability -- E, B, T,
 * lenMSB, sealed and otype fields are not present in all formats and are
 * populated by capBitsToCapability.
 */
struct Capability = {
  tag                    : bool    ,
  uperms                 : bits(4) ,
  permit_set_CID         : bool    ,
  access_system_regs     : bool    ,
  permit_unseal          : bool    ,
  permit_ccall           : bool    ,
  permit_seal            : bool    ,
  permit_store_local_cap : bool    ,
  permit_store_cap       : bool    ,
  permit_load_cap        : bool    ,
  permit_store           : bool    ,
  permit_load            : bool    ,
  permit_execute         : bool    ,
  global                 : bool    ,
  reserved               : bits(2) ,
  flag_cap_mode          : bool    ,
  internal_e             : bool    ,
  E                      : bits(6) ,
  sealed                 : bool    ,
  B                      : bits(14),
  T                      : bits(14),
  otype                  : bits(18),
  address                : bits(64)
}

/* Reset E and T calculated to make top 2**64. */
let maxE = 52
let resetE = to_bits(6, maxE)
let resetT = 0b01 @ 0x000 /* bit 12 set */

let null_cap : Capability = struct {
  tag                    = false,
  uperms                 = zeros(),
  permit_set_CID         = false,
  access_system_regs     = false,
  permit_unseal          = false,
  permit_ccall           = false,
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
  internal_e             = true,
  E                      = resetE,
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = ones(),
  address                = zeros()
}

let default_cap : Capability = struct {
  tag                    = true,
  uperms                 = ones(),
  permit_set_CID         = true,
  access_system_regs     = true,
  permit_unseal          = true,
  permit_ccall           = true,
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
  internal_e             = true,
  E                      = resetE,
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = ones(),
  address                = zeros()
}

/* Convert from capabilty bits (128 bits with tag) to a more convenient struct. */
function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = {
  internal_exponent : bool = c[90];
  otype : bits(18) = c[108..91];
  let sealed : bool = otype != ones();
  E : bits(6)  = zeros();
  Bs : bits(14) = zeros();
  T : bits(12) = zeros();
  lenMSBs : bits(2) = zeros();
  if internal_exponent then {
    /* Exponent stored instead of T[2..0] and B[2..0] */
    E = c[80..78] @ c [66..64];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    T = c[89..81] @ 0b000;
    Bs = c[77..67] @ 0b000;
  } else {
    /* Exponent zero */
    lenMSBs = 0b00;
    T = c[89..78];
    Bs = c[77..64];
  };
  /* Reconstruct top two bits of T given T = B + len and:
   * 1) the top two bits of B
   * 2) most significant two bits of length derived from format above
   * 3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
   */
  carry_out = if T <_u Bs[11..0] then 0b01 else 0b00;
  Ttop2 = Bs[13..12] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = c[127..124],
    permit_set_CID         = c[123],
    access_system_regs     = c[122],
    permit_unseal          = c[121],
    permit_ccall           = c[120],
    permit_seal            = c[119],
    permit_store_local_cap = c[118],
    permit_store_cap       = c[117],
    permit_load_cap        = c[116],
    permit_store           = c[115],
    permit_load            = c[114],
    permit_execute         = c[113],
    global                 = c[112],
    reserved               = c[111..110],
    flag_cap_mode          = c[109],
    internal_e             = internal_exponent,
    E                      = E,
    sealed                 = sealed,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = otype,
    address                = c[63..0]
  }
}

/*
function fastRepCheck(c, i) : (Capability, bits(64)) -> bool=
    let 'E = unsigned(c.E) in
    if (E >= maxE) then
        true /* in this case representable region is whole address space */
    else
        let E'       = min(E, maxE) in
        let i_top    = signed(i >>_s (E+23)) in
        let i_mid : bits(23) = truncate(i >>_s E)in
        let a_mid : bits(23) = truncate(c.address >> E) in
        let R : bits(20)     = (c.B) - 0x01000 in
        let diff : bits(20)  = R - a_mid in
        let diff1 : bits(20) = diff - 1 in
        /* i_top determines 1. whether the increment is inRange
           i.e. less than the size of the representable region
           (2**(E+20)) and 2. whether it is positive or negative. To
           satisfy 1. all top bits must be the same so we are
           interested in the cases i_top is 0 or -1 */
        if (i_top == 0) then
          i_mid <_u diff1
        else if (i_top == -1) then
          (i_mid >=_u diff) & (R != a_mid)
        else
          false
*/
