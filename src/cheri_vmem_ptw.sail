/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// ****************************************************************
// PTW exceptions

// 'ext_ptw' supports (non-standard) extensions to the default addr-translation and PTW.
// See riscv_types_ext.sail for definitions.

// Failure modes for address-translation/page-table-walks
// PRIVATE
union PTW_Error = {
  PTW_Invalid_Addr  : unit,          // invalid source address
  PTW_Access        : unit,          // physical memory access error for a PTE
  PTW_Invalid_PTE   : unit,
  PTW_No_Permission : unit,
  PTW_Misaligned    : unit,          // misaligned superpage
  PTW_PTE_Update    : unit,          // PTE update needed but not enabled
  PTW_Ext_Error     : ext_ptw_error  // parameterized for errors from extensions
}

// PRIVATE: only 'to_str' overload is public
function ptw_error_to_str(e : PTW_Error) -> string = {
  match e {
    PTW_Invalid_Addr()   => "invalid-source-addr",
    PTW_Access()         => "mem-access-error",
    PTW_Invalid_PTE()    => "invalid-pte",
    PTW_No_Permission()  => "no-permission",
    PTW_Misaligned()     => "misaligned-superpage",
    PTW_PTE_Update()     => "pte-update-needed",
    PTW_Ext_Error(e)     => "extension-error"
  }
}

// PUBLIC
overload to_str = {ptw_error_to_str}

function ext_get_ptw_error(eptwf : ext_ptw_fail) -> PTW_Error =
  match (eptwf) {
    EPTWF_NO_PERM  => PTW_No_Permission(),
    EPTWF_CAP_ERR  => PTW_Ext_Error(AT_CAP_ERR)
  }

// Convert translation/PTW failures into architectural exceptions
function translationException(a : AccessType(ext_access_type),
                              f : PTW_Error)
                             -> ExceptionType = {
  match (a, f) {
    /* Tag-asserting stores can raise CHERI page faults. */
    (Write(Cap), PTW_Ext_Error(AT_CAP_ERR))        => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),
    (ReadWrite(Cap, _), PTW_Ext_Error(AT_CAP_ERR)) => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),
    (ReadWrite(_, Cap), PTW_Ext_Error(AT_CAP_ERR)) => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),

    /* No other operations should raise CHERI-specific page faults */
    (_, PTW_Ext_Error(_))                          => internal_error(__FILE__, __LINE__, "Unexpected PTW Extension Error"),

    /* For other exceptions, Cap and Data accesses fault in the same way. */
    (ReadWrite(_, _), PTW_Access())                => E_SAMO_Access_Fault(),
    (ReadWrite(_, _), _)                           => E_SAMO_Page_Fault(),
    (Read(_), PTW_Access())                        => E_Load_Access_Fault(),
    (Read(_), _)                                   => E_Load_Page_Fault(),
    (Write(_), PTW_Access())                       => E_SAMO_Access_Fault(),
    (Write(_), _)                                  => E_SAMO_Page_Fault(),

    (Execute(), PTW_Access())                      => E_Fetch_Access_Fault(),
    (Execute(), _)                                 => E_Fetch_Page_Fault()
  }
}
