/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* CHERI interface to physical memory.  We use the metadata facility for tags. */

val mem_read_cap_optpriv : (OptPrivilege, xlenbits, bool, bool, bool) -> MemoryOpResult(Capability) effect {rmem, rmemt, rreg, escape}
function mem_read_cap_optpriv (optpriv, addr, aq, rl, res) = {
  let result : MemoryOpResult((CapBits, bool)) =
    match optpriv {
      PrivDefault() => mem_read_meta(Read(Data), addr, cap_size, aq, rl, res, true),
      PrivOverride(p) => mem_read_priv_meta(Read(Data), p, addr, cap_size, aq, rl, res, true)
    };
  match result {
    MemValue(v, tag) => MemValue(memBitsToCapability(tag, v)),
    MemException(e)  => MemException(e) : MemoryOpResult(Capability)
  }
}

val mem_read_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(Capability) effect {rmem, rmemt, rreg, escape}
function mem_read_cap (addr, aq, rl, res) =
  mem_read_cap_optpriv(PrivDefault(), addr, aq, rl, res)

val mem_read_optpriv : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), OptPrivilege, xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(bits(8 * 'n)) effect {rmem, rmemt, rreg, escape}
function mem_read_optpriv (typ, optpriv, paddr, width, aq, rl, res) = {
  match optpriv {
    PrivDefault() => mem_read(typ, paddr, width, aq, rl, res),
    PrivOverride(p) => mem_read_priv(typ, p, paddr, width, aq, rl, res)
  }
}

val mem_write_ea_cap : (xlenbits, bool, bool, bool) -> MemoryOpResult(unit) effect {eamem}
function mem_write_ea_cap(addr, aq, rl, con) = {
  if   ~(is_aligned_addr(addr, cap_size))
  then MemException(E_SAMO_Addr_Align())
  else MemValue(__write_mem_ea(Write_plain, sizeof(xlen), addr, cap_size)) // FIXME: is Write_plain correct?
}

val mem_write_cap_optpriv : (OptPrivilege, xlenbits, Capability, bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape, wmvt}
function mem_write_cap_optpriv (optpriv, addr, cap, aq, rl, con) = {
  let cap_bits = capToMemBits(cap);
  /* Assume that conversion to bits and back does not change the capability.
     TODO: State closed-form normalised-ness criterion that implies this,
     and prove it as an invariant of capabilities in the system. */
  assert(memBitsToCapability(cap.tag, cap_bits) == cap);
  match optpriv {
    PrivDefault() => mem_write_value_meta(addr, cap_size, cap_bits, Cap, cap.tag, aq, rl, con),
    PrivOverride(p) => mem_write_value_priv_meta(addr, cap_size, cap_bits, Write(Cap), p, cap.tag, aq, rl, con)
  }
}

val mem_write_cap : (xlenbits, Capability, bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, rreg, wreg, escape, wmvt}
function mem_write_cap (addr, cap, aq, rl, con) = mem_write_cap_optpriv(PrivDefault(), addr, cap, aq, rl, con)

val mem_write_value_optpriv : forall 'n, 0 < 'n <= max_mem_access . (OptPrivilege, xlenbits, atom('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(bool) effect {wmv, wmvt, rreg, wreg, escape}
function mem_write_value_optpriv (optpriv, addr, width, value, aq, rl, con) = {
  match optpriv {
    PrivDefault() => mem_write_value(addr, width, value, aq, rl, con),
    PrivOverride(p) => mem_write_value_priv(addr, width, value, p, aq, rl, con)
  }
}
