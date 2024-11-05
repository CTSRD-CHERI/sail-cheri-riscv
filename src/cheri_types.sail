/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

enum CPtrCmpOp = {
  CEQ,
  CNE,
  CLT,
  CLE,
  CLTU,
  CLEU,
  CEXEQ,
  CNEXEQ
}

enum ClearRegSet = {
  GPRegs,
  FPRegs
}

enum CapEx = {
  CapEx_TagViolation,
  CapEx_SealViolation,
  CapEx_PermissionViolation,
  CapEx_InvalidAddressViolation,
  CapEx_LengthViolation,
}

mapping capex_code : CapEx <-> bits(4) = {
  CapEx_TagViolation            <-> 0x0,
  CapEx_SealViolation           <-> 0x1,
  CapEx_PermissionViolation     <-> 0x2,
  CapEx_InvalidAddressViolation <-> 0x3,
  CapEx_LengthViolation         <-> 0x4,
}

mapping capex_name : CapEx <-> string = {
  CapEx_TagViolation            <-> "TagViolation",
  CapEx_SealViolation           <-> "SealViolation",
  CapEx_PermissionViolation     <-> "PermissionViolation",
  CapEx_InvalidAddressViolation <-> "InvalidAddressViolation",
  CapEx_LengthViolation         <-> "LengthViolation",
}

enum CapCheckType = {
  CapCheckType_Inst,
  CapCheckType_Data,
  CapCheckType_JBr,
}

mapping capchecktype_code : CapCheckType <-> bits(4) = {
  CapCheckType_Inst <-> 0x0,
  CapCheckType_Data <-> 0x1,
  CapCheckType_JBr  <-> 0x2,
}

mapping capchecktype_name : CapCheckType <-> string = {
  CapCheckType_Inst <-> "InstructionAccessFault",
  CapCheckType_Data <-> "LdStAmoDataFault",
  CapCheckType_JBr  <-> "JBrFault",
}

// Options for the M mode bit.
enum ExecutionMode = {
  IntPtrMode,
  CapPtrMode,
}

// Encoding of the M bit.
mapping execution_mode_encdec : ExecutionMode <-> bits(1) = {
  IntPtrMode <-> 0b1,
  CapPtrMode <-> 0b0,
}

// Decoded permission bits with architectural interpretation.
struct ArchPerms = {
  R : bool,
  W : bool,
  C : bool,
  X : bool,
  LM : bool,
  ASR : bool
}

let null_perms : ArchPerms = struct { R=false, W=false, C=false, X=false, LM=false, ASR=false }
