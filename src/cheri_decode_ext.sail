/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function ext_decode_compressed(bv : bits(16)) -> ast = {
  match effective_cheri_mode() {
    CapPtrMode => {
      match(encdec_compressed_capmode(bv)) {
        /* Use the default decoding for non-capmode encodings. */
        NOT_C_CAPMODE(_) => encdec_compressed(bv),
        C_CAPMODE_AST => C_CAPMODE_AST
      }
    },
    IntPtrMode => encdec_compressed(bv),
  }
}

function ext_decode(bv : bits(32)) -> ast = {
  match effective_cheri_mode() {
    CapPtrMode => {
      match(encdec_capmode(bv)) {
        /* Use the default decoding for non-capmode encodings. */
        NOT_CAPMODE(_) => encdec(bv),
        CAPMODE_AST => CAPMODE_AST
      }
    },
    IntPtrMode => encdec(bv),
  }
}
