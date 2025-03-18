/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// Type constraint that checks if 'v is a valid virtual memory mode size.
type is_sv_mode('v) -> Bool = 'v in {32, 39, 48, 57}

// Range of possible page levels depending on the virtual memory mode:
//
//   Sv32 = range(0, 1)
//   Sv39 = range(0, 2)
//   Sv48 = range(0, 3)
//   Sv57 = range(0, 4)
//
type level_range('v), is_sv_mode('v) =
  range(0, (if 'v == 32 then 1 else (if 'v == 39 then 2 else (if 'v == 48 then 3 else 4))))

// Size of a Page Table Entry, depending on the virtual memory mode.
type pte_bits('v), is_sv_mode('v) = bits(if 'v == 32 then 32 else 64)

// Number of Physical Page Number bits, depending on the virtual memory mode.
type ppn_bits('v), is_sv_mode('v) = bits(if 'v == 32 then 22 else 44)

// Number of Virtual Page Number bits, depending on the virtual memory mode.
type vpn_bits('v), is_sv_mode('v) = bits('v - pagesize_bits)


// This enum is used for reads and writes and has slighly different
// meanings in each case.
enum ext_access_type = {
  // Writes: Non-capability writes, or writes of untagged capabilities.
  // Reads: Non-capability reads.
  Data,
  // Writes: Writes of tagged capabilities
  // Reads: Capability reads. (It may or may not end up being tagged but it *could* be tagged.)
  Tagged,
}

let default_write_acc : ext_access_type = Data

// Return true if we are writing a tagged capability.
function isTaggedWrite(ac : AccessType(ext_access_type)) -> bool =
  match ac {
    Write(Tagged) => true,
    ReadWrite(_, Tagged) => true,
    _ => false,
  }

// Return true if we are reading a capability (which may be tagged).
function isTaggedRead(ac : AccessType(ext_access_type)) -> bool =
  match ac {
    Read(Tagged) => true,
    ReadWrite(Tagged, _) => true,
    _ => false,
  }

val accessType_to_str : AccessType(ext_access_type) -> string
function accessType_to_str (a) =
  match a {
    Read(Data)                => "R",
    Write(Data)               => "W",
    Read(Tagged)              => "Rc",
    Write(Tagged)             => "Wc",
    ReadWrite(Data, Data)     => "RW",
    ReadWrite(Data, Tagged)   => "RWc",
    ReadWrite(Tagged, Data)   => "RcW",
    ReadWrite(Tagged, Tagged) => "RcWc",
    Execute()                 => "X",
    Cache(CleanFlush)         => "CACHE.CLEANFLUSH",
    Cache(Inval)              => "CACHE.INVAL",
    Cache(Zero)               => "CACHE.ZERO",
  }

overload to_str = {accessType_to_str}
