// Registers added for CHERI. Note that extended pre-existing registers are
// not included here. Their names will lack the extra "C".

// We don't need to add these to ext_read_CSR() or ext_write_CSR() since those
// functions are for XLEN reads/writes which will never go through the non-CHERI
// handle_csr_op().

function clause is_CSR_defined(0x416) = cheri_registers_enabled() // ddc
function clause is_CSR_defined(0x74c) = cheri_registers_enabled() // mtdc
function clause is_CSR_defined(0x163) = cheri_registers_enabled() // stdc
function clause is_CSR_defined(0x780) = haveZstid() // mtidc
function clause is_CSR_defined(0x580) = haveZstid() // stidc
function clause is_CSR_defined(0x480) = haveZstid() // utidc
function clause is_CSR_defined(0x7bc) = cheri_registers_enabled() & debug_mode_active // dddc
function clause is_CSR_defined(0x7bd) = cheri_registers_enabled() & debug_mode_active // dinfc


mapping clause csr_name_map = 0x416 <-> "ddc"
mapping clause csr_name_map = 0x74c <-> "mtdc"
mapping clause csr_name_map = 0x163 <-> "stdc"
mapping clause csr_name_map = 0x780 <-> "mtid"
mapping clause csr_name_map = 0x580 <-> "stid"
mapping clause csr_name_map = 0x480 <-> "utid"
mapping clause csr_name_map = 0x7bc <-> "dddc"
mapping clause csr_name_map = 0x7bd <-> "dinfc"

// XLEN CSRs for CHERI

function clause is_CSR_defined(0x34b) = true // mtval2
function clause is_CSR_defined(0x14b) = true // stval2

mapping clause csr_name_map = 0x34b <-> "mtval2"
mapping clause csr_name_map = 0x14b <-> "stval2"

function clause read_CSR(0x34b, _) = mtval2.bits
function clause write_CSR(0x34b, value) = { mtval2 = legalize_tval2(mtval2, value); mtval2.bits }
function clause read_CSR(0x14b, _) = stval2.bits
function clause write_CSR(0x14b, value) = { stval2 = legalize_tval2(stval2, value); stval2.bits }
