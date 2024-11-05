/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

type log2_cap_size : Int = 3
let  log2_cap_size = sizeof(log2_cap_size)

// Software Defined Permissions
type cap_sd_perms_width : Int = 2
let  cap_sd_perms_width = sizeof(cap_sd_perms_width)

// Width of reserved fields. Their values need to be preserved.
type cap_reserved_1_width : Int = 1
let  cap_reserved_1_width = sizeof(cap_reserved_1_width)
type cap_reserved_0_width : Int = 3
let  cap_reserved_0_width = sizeof(cap_reserved_0_width)

// Width of the decoded B and T fields.
type cap_mantissa_width : Int = 10
let  cap_mantissa_width = sizeof(cap_mantissa_width)

// Bits required for maximum exponent.
// TODO: If Sail had clog2 support we could calculate this from cap_max_E.
type cap_E_width : Int  = 5
let  cap_E_width = sizeof(cap_E_width)

// Bits required for Architectural Permissions and Mode
type cap_AP_M_width : Int = 5
let  cap_AP_M_width = sizeof(cap_AP_M_width)

// Whether setbounds can use the L8 bit for extra precision in the implied E=0 case.
let cap_use_L8 : bool = true

// Capability format metadata completely compressed. Tag is out of band.
bitfield EncMetadata : bits(32) = {
  // Software Defined Permissions.
  SDP        : 31 .. 30,
  // Architectural Permissions and Mode (encoded together).
  AP_M       : 29 .. 25,
  // Upper reserved area doesn't exist but Sail's syntax doesn't allow zero width
  // fields here, so just steal a bit from the other one.
  reserved_1 : 24,
  // Lower reserved area.
  reserved_0 : 23 .. 21,
  // Capability Type bit.
  CT         : 20,
  // Exponent Format.
  EF         : 19,
  // Either MSB of exponent or MSB of length depending on EF.
  L8         : 18,
  // Top bits, not including L8 or TE.
  Tm         : 17 .. 12,
  // Lowest bits of T, that may be part of the exponent depending on EF.
  TE         : 11 .. 10,
  // Bottom bits, not including BE.
  Bm         : 9 .. 2,
  // Lowest bits of B, that may be part of the exponent depending on EF.
  BE         : 1 .. 0,
}

type CapAP_M = bits(5)

// 32-bit permission encoding/decoding, converting between the the encoded bits compressed into the capability
// and the architectural fields.
// Forwards match failures mean bit permissions have been directly changed e.g. with SCHI. These should be
// checked for outside the function, and the null fields returned.
// Backwards match failures occur when encoding an unrepresentable combination of fields: this should be
// prevented by calling legalizeFields when changing the fields.
mapping ap_m_encdec : bits(cap_AP_M_width) <-> (ArchPerms, ExecutionMode) = {
  // Quadrant 0: Non-capability data read/write
  0b00 @ 0b000     <-> (struct{ R=false, W=false, C=false, LM=false, X=false, ASR=false }, execution_mode_encdec(0b0)),
  0b00 @ 0b001     <-> (struct{ R= true, W=false, C=false, LM=false, X=false, ASR=false }, execution_mode_encdec(0b0)),
  0b00 @ 0b100     <-> (struct{ R=false, W= true, C=false, LM=false, X=false, ASR=false }, execution_mode_encdec(0b0)),
  0b00 @ 0b101     <-> (struct{ R= true, W= true, C=false, LM=false, X=false, ASR=false }, execution_mode_encdec(0b0)),
  // Quadrant 1: Executable capabilities
  0b01 @ 0b00 @ m  <-> (struct{ R= true, W= true, C= true, LM= true, X= true, ASR= true }, execution_mode_encdec(m)),
  0b01 @ 0b01 @ m  <-> (struct{ R= true, W=false, C= true, LM= true, X= true, ASR=false }, execution_mode_encdec(m)),
  0b01 @ 0b10 @ m  <-> (struct{ R= true, W= true, C= true, LM= true, X= true, ASR=false }, execution_mode_encdec(m)),
  0b01 @ 0b11 @ m  <-> (struct{ R= true, W= true, C=false, LM=false, X= true, ASR=false }, execution_mode_encdec(m)),
  // Quadrant 2: Restricted capability data read/write
  0b10 @ 0b011     <-> (struct{ R= true, W=false, C= true, LM=false, X=false, ASR=false }, execution_mode_encdec(0b0)),
  // Quadrant 3: Capability data read/write
  0b11 @ 0b011     <-> (struct{ R= true, W=false, C= true, LM= true, X=false, ASR=false }, execution_mode_encdec(0b0)),
  0b11 @ 0b111     <-> (struct{ R= true, W= true, C= true, LM= true, X=false, ASR=false }, execution_mode_encdec(0b0)),
}

// Ideally ap_m_encdec(({null,infinite}_perms, IntPtrMode)), but spurious incomplete match side-effect at toplevel
let null_ap_m     = 0b00000
let infinite_ap_m = 0b01001

// Perform the XLEN-specific ACPERMS legalization.
function legalizePermsAndMode(perms : ArchPerms, mode : ExecutionMode) -> (ArchPerms, ExecutionMode) = {
  let perms = if perms.R & perms.W & perms.X & perms.ASR & perms.C & perms.LM then perms else {perms with ASR=false};
  let perms = if perms.R then perms else {perms with C=false, X=false};
  let perms = if perms.X & perms.R & not(perms.C) & not(perms.W) then {perms with X=false} else perms;
  let mode = if perms.X then mode else execution_mode_encdec(0b0);
  let perms = if perms.C then perms else {perms with LM=false};
  let perms = if perms.C & not(perms.LM) then {perms with W=false} else perms;
  // "If removing LM-permission results in unrepresentable permissions, then set R-permission and C-permission only."
  let (perms, mode) = if ap_m_encdec_backwards_matches((perms, mode)) then (perms, mode) else {
    ({null_perms with R=true, C=true}, execution_mode_encdec(0b0))
  };
  (perms, mode)
}

// Needed because there's no L8 in the RV64 version.
function getMetadataL8(meta : EncMetadata) -> bits(1) = meta[L8]
function setMetadataL8(meta : EncMetadata, L8 : bits(1)) -> EncMetadata =
  [ meta with L8=L8 ]

// Get the internal exponent. This is only meaningful if EF is "internal".
function getMetadataInternalExponent(meta : EncMetadata) -> bits(cap_E_width) =
  meta[L8] @ meta[TE] @ meta[BE]
