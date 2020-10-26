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
type cap_size : Int = 8
let cap_size = sizeof(cap_size)
type log2_cap_size : Int = 3
let log2_cap_size = sizeof(log2_cap_size)
type CapBits = bits(8 * cap_size)
/* width of otype field in bits */
type cap_otype_width : Int = 4
let cap_otype_width = sizeof(cap_otype_width)
type cap_hperms_width : Int = 12
let cap_hperms_width = sizeof(cap_hperms_width)
type cap_uperms_width : Int = 0
let cap_uperms_width = sizeof(cap_uperms_width)
type cap_addr_width : Int = xlen
let  cap_addr_width = sizeof(cap_addr_width)
type cap_len_width : Int = xlen + 1
let  cap_len_width  = sizeof(cap_len_width)
type cap_mantissa_width : Int = 8
let cap_mantissa_width = sizeof(cap_mantissa_width)

/* For CLoadTags and CClearTags, which operate at cache line granularity */
type caps_per_cache_line : Int = 8
let  caps_per_cache_line = sizeof(caps_per_cache_line)

let MAX_ADDR = MAX(cap_addr_width)
type CapAddrInt = range(0, (2 ^ cap_addr_width) - 1)
type CapLen = range(0, 2 ^ 33) /* XXX sail can't handle if this is expressed as cap_len_width */

/*!
 * A partially decompressed version of a capability, populated by
 * capBitsToCapability. E is not present in all formats.
 */
struct Capability = {
  tag                    : bool    ,
  uperms                 : bits(cap_uperms_width) ,
  permit_set_CID         : bool    ,
  access_system_regs     : bool    ,
  permit_unseal          : bool    ,
  permit_cinvoke         : bool    ,
  permit_seal            : bool    ,
  permit_store_local_cap : bool    ,
  permit_store_cap       : bool    ,
  permit_load_cap        : bool    ,
  permit_store           : bool    ,
  permit_load            : bool    ,
  permit_execute         : bool    ,
  global                 : bool    ,
  reserved               : bits(0) ,
  flag_cap_mode          : bool    ,
  internal_e             : bool    ,
  E                      : bits(6) ,
  B                      : bits(cap_mantissa_width),
  T                      : bits(cap_mantissa_width),
  otype                  : bits(cap_otype_width),
  address                : bits(cap_addr_width),
}

/* Reset E and T calculated to make top 2**32. */
let maxE = 26
let internal_exponent_take_bits = 3
let resetE = to_bits(6, maxE)
let resetT = 0b01000000 /* bit 6 set */

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
  internal_e             = true,
  E                      = resetE,
  B                      = zeros(),
  T                      = resetT,
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
  internal_e             = true,
  E                      = resetE,
  B                      = zeros(),
  T                      = resetT,
  otype                  = to_bits(cap_otype_width, otype_unsealed),
  address                = zeros()
}

/* Convert from capabilty bits (64 bits with tag) to a more convenient struct. */
function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = {
  internal_exponent : bool = bit_to_bool(c[46]);
  otype : bits(4) = c[50..47];
  E : bits(6)  = zeros();
  Bs : bits(8) = zeros();
  T : bits(6) = zeros();
  lenMSBs : bits(2) = zeros();
  if internal_exponent then {
    /* Exponent stored instead of T[2..0] and B[2..0] */
    E = c[42..40] @ c [34..32];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    T = c[45..43] @ 0b000;
    Bs = c[39..35] @ 0b000;
  } else {
    /* Exponent zero */
    lenMSBs = 0b00;
    T = c[45..40];
    Bs = c[39..32];
  };
  /* Reconstruct top two bits of T given T = B + len and:
   * 1) the top two bits of B
   * 2) most significant two bits of length derived from format above
   * 3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
   */
  carry_out = if T <_u Bs[5..0] then 0b01 else 0b00;
  Ttop2 = Bs[7..6] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = [],
    permit_set_CID         = bit_to_bool(c[63]),
    access_system_regs     = bit_to_bool(c[62]),
    permit_unseal          = bit_to_bool(c[61]),
    permit_cinvoke         = bit_to_bool(c[60]),
    permit_seal            = bit_to_bool(c[59]),
    permit_store_local_cap = bit_to_bool(c[58]),
    permit_store_cap       = bit_to_bool(c[57]),
    permit_load_cap        = bit_to_bool(c[56]),
    permit_store           = bit_to_bool(c[55]),
    permit_load            = bit_to_bool(c[54]),
    permit_execute         = bit_to_bool(c[53]),
    global                 = bit_to_bool(c[52]),
    reserved               = [],
    flag_cap_mode          = bit_to_bool(c[51]),
    internal_e             = internal_exponent,
    E                      = E,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = otype,
    address                = c[31..0]
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

