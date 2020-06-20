/* Extension for CHERI PTE checks */
enum pte_check = {PTE_CAP_OK, PTE_LOAD_CAP_ERR, PTE_STORE_CAP_ERR}

/* Extension for CHERI page-table-walks */

enum ext_ptw = {PTW_CAP_OK, PTW_LOAD_CAP_ERR, PTW_STORE_CAP_ERR}

let init_ext_ptw : ext_ptw = PTW_CAP_OK /* initial value of the PTW accumulator */

/* Default accumulation of PTE check extensions into PTW accumulator */
function ext_accum_ptw_result(ptw : ext_ptw, pte : pte_check) -> ext_ptw =
  match (ptw, pte) {
    (PTW_CAP_OK, PTE_CAP_OK)        => PTW_CAP_OK,
    (PTW_CAP_OK, PTE_LOAD_CAP_ERR)  => PTW_LOAD_CAP_ERR,
    (PTW_CAP_OK, PTE_STORE_CAP_ERR) => PTW_STORE_CAP_ERR,

    /* CHECK ME: The below prioritizes store exceptions over load tag stripping. */

    (PTW_LOAD_CAP_ERR, PTE_CAP_OK)        => PTW_LOAD_CAP_ERR,
    (PTW_LOAD_CAP_ERR, PTE_LOAD_CAP_ERR)  => PTW_LOAD_CAP_ERR,
    (PTW_LOAD_CAP_ERR, PTE_STORE_CAP_ERR) => PTW_STORE_CAP_ERR,

    (PTW_STORE_CAP_ERR, _ )               => PTW_STORE_CAP_ERR
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
