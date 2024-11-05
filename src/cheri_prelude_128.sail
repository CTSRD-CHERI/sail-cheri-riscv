/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

type log2_cap_size : Int = 4
let  log2_cap_size = sizeof(log2_cap_size)

// Software Defined Permissions
type cap_sd_perms_width : Int = 4
let  cap_sd_perms_width = sizeof(cap_sd_perms_width)

// Width of reserved fields. Their values need to be preserved.
type cap_reserved_1_width : Int = 7
let  cap_reserved_1_width = sizeof(cap_reserved_1_width)
type cap_reserved_0_width : Int = 18
let  cap_reserved_0_width = sizeof(cap_reserved_0_width)

// Width of the decoded B and T fields.
type cap_mantissa_width : Int = 14
let  cap_mantissa_width = sizeof(cap_mantissa_width)

// Bits required for maximum exponent.
// TODO: If Sail had clog2 support we could calculate this from cap_max_E.
type cap_E_width : Int  = 6
let  cap_E_width = sizeof(cap_E_width)

// Bits required for Architectural Permissions and Mode
type cap_AP_M_width : Int = 7
let  cap_AP_M_width = sizeof(cap_AP_M_width)

// Whether setbounds can use the L8 bit for extra precision in the implied E=0 case.
let cap_use_L8 : bool = false

// Capability format metadata completely compressed. Tag is out of band.
bitfield EncMetadata : bits(64) = {
  // Upper reserved area (64-bit only).
  reserved_1 : 63 .. 57,
  // Software Defined Permissions.
  SDP        : 56 .. 53,
  // Architectural Permissions and Mode (encoded together).
  AP_M       : 52 .. 46,
  // Lower reserved area.
  reserved_0 : 45 .. 28,
  // Capability Type bit.
  CT         : 27,
  // Exponent Format.
  EF         : 26,
  // Top bits, not including TE.
  Tm         : 25 .. 17,
  // Lowest bits of T, that may be part of the exponent depending on EF.
  TE         : 16 .. 14,
  // Bottom bits, not including BE.
  Bm         : 13 .. 3,
  // Lowest bits of B, that may be part of the exponent depending on EF.
  BE         : 2 .. 0,
}

// 64-bit permission encoding/decoding, converting between the bitvector representation and the
// encoded bits compressed into the capability.
// This is the identity mapping (subject to reordering) but detects reserved combinations.
// Forwards match failures mean bit permissions have been directly changed e.g. with SCHI. These should be
// checked for outside the function, and the null fields returned.
// Backwards match failures occur when encoding an unrepresentable combination of fields: this should be
// prevented by calling legalizeFields when changing the fields.
mapping ap_m_encdec : bits(cap_AP_M_width) <-> (ArchPerms, ExecutionMode) = {
  execution_mode_encdec(M) @ bool_bits(LM) @ bool_bits(ASR) @ bool_bits(X) @ bool_bits(R) @ bool_bits(W) @ bool_bits(C)
    if (not(ASR) | X) & (not(C) | (R | W)) & (M == execution_mode_encdec(0b0) | X) & (not(LM) | C) <->
  (struct{R, W, C, X, LM, ASR}, M)
    if (not(ASR) | X) & (not(C) | (R | W)) & (M == execution_mode_encdec(0b0) | X) & (not(LM) | C),
}

// Ideally ap_m_encdec(({null,infinite}_perms, IntPtrMode)), but spurious incomplete match side-effect at toplevel
let null_ap_m     = 0b0000000
let infinite_ap_m = 0b1111111

// Perform the XLEN-specific ACPERMS legalization.
function legalizePermsAndMode(perms : ArchPerms, mode : ExecutionMode) -> (ArchPerms, ExecutionMode) = {
  let perms = if perms.X then perms else {perms with ASR=false};
  let perms = if perms.R | perms.W then perms else {perms with C=false};
  let mode = if perms.X then mode else execution_mode_encdec(0b0);
  let perms = if perms.C then perms else {perms with LM=false};
  (perms, mode)
}

// Needed because there's no L8 in the RV64 version.
function getMetadataL8(meta : EncMetadata) -> bits(1) = 0b0
function setMetadataL8(meta : EncMetadata, L8 : bits(1)) -> EncMetadata = meta

// Get the internal exponent. This is only meaningful if EF is "internal".
function getMetadataInternalExponent(meta : EncMetadata) -> bits(cap_E_width) =
  meta[TE] @ meta[BE]
