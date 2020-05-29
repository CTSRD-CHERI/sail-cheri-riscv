/*
 * Extension for CHERI page table walker
 *
 * We are going to carry around a summary of the PTW walk for data-dependent
 * (well, tag-dependent) behaviors by the instructions.
 */

enum ext_ptw_lc = {
  /* Tags flow as might be expected */
  PTW_LC_OK,

  /* PTE settings require clearing tags */
  PTW_LC_CLEAR
}

enum ext_ptw_sc = {
  /* Tag stores are permitted */
  PTW_SC_OK,

  /* Tag-asserting stores trap */
  PTW_SC_TRAP
}

struct ext_ptw = {
  ptw_lc : ext_ptw_lc,
  ptw_sc : ext_ptw_sc
}

function ext_ptw_lc_join(e : ext_ptw, l : ext_ptw_lc) -> ext_ptw =
  { e with ptw_lc =
      match l {
        PTW_LC_OK => e.ptw_lc,
        PTW_LC_CLEAR => l
      }
  }

function ext_ptw_sc_join(e : ext_ptw, s : ext_ptw_sc) -> ext_ptw =
  { e with ptw_sc =
      match s {
        PTW_SC_OK => e.ptw_sc,
        PTW_SC_TRAP => s
      }
  }

/* initial value of the PTW accumulator */
let init_ext_ptw : ext_ptw = struct {
  ptw_lc = PTW_LC_OK,
  ptw_sc = PTW_SC_OK
}

/* Address translation errors */
enum ext_ptw_error = {AT_CAP_ERR}

/* CHERI exception extensions */

enum ext_exc_type = {
  EXC_LOAD_CAP_PAGE_FAULT,
  EXC_SAMO_CAP_PAGE_FAULT,
  EXC_CHERI
}

/* CHERI conversion of extension exceptions to bits */
val ext_exc_type_to_bits : ext_exc_type -> exc_code
function ext_exc_type_to_bits(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 0x1a,
    EXC_SAMO_CAP_PAGE_FAULT => 0x1b,
    EXC_CHERI               => 0x1c
  }

/* CHERI conversion of extension exceptions to integers */
val num_of_ext_exc_type : ext_exc_type -> {'n, (0 <= 'n < xlen). int('n)}
function num_of_ext_exc_type(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 26,
    EXC_SAMO_CAP_PAGE_FAULT => 27,
    EXC_CHERI               => 28
  }

/* CHERI conversion of extension exceptions to strings */
val ext_exc_type_to_str : ext_exc_type -> string
function ext_exc_type_to_str(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => "load-cap-page-fault",
    EXC_SAMO_CAP_PAGE_FAULT => "store/amo-cap-page-fault",
    EXC_CHERI               => "cheri"
  }
