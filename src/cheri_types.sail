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

enum CheriPageAccess = {
  CheriPage_Ld,
  CheriPage_St
}

union CapCheckType = {
  CapCheckType_Inst : unit,
  CapCheckType_Ld : unit,
  CapCheckType_St : unit,
  CapCheckType_Pte : CheriPageAccess,
}

mapping capchecktype_name : CapCheckType <-> string = {
  CapCheckType_Inst() <-> "Instruction Access",
  CapCheckType_Ld() <-> "Load Access",
  CapCheckType_St() <-> "Store Access",
  CapCheckType_Pte(CheriPage_Ld) <-> "Load Page",
  CapCheckType_Pte(CheriPage_St) <-> "Store/Amo Page",
}

// Options for the P mode bit.
enum PointerMode = {
  IntPtrMode,
  CapPtrMode,
}

// Encoding of the P bit.
mapping pointer_mode_encdec : PointerMode <-> bits(1) = {
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
  SL : bool,
  EL : bool,
  ASR : bool
}

let null_perms : ArchPerms = struct { R=false, W=false, C=false, X=false, LM=false, SL=false, EL=false, ASR=false }
