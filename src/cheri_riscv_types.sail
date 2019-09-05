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
enum ext_ptw_error = {AT_LOAD_CAP_ERR, AT_STORE_CAP_ERR}

/* CHERI exception extensions */

enum ext_exc_type = {EXC_CHERI, EXC_CHERI_VMEM_LOAD_CAP, EXC_CHERI_VMEM_STORE_CAP}

/* CHERI translation of PTW errors into exception annotations */
function ext_translate_exception(e : ext_ptw_error) -> ext_exc_type =
  match e {
    AT_LOAD_CAP_ERR  => EXC_CHERI_VMEM_LOAD_CAP,
    AT_STORE_CAP_ERR => EXC_CHERI_VMEM_STORE_CAP
}
