// Registers added for CHERI. Note that extended pre-existing registers are
// not included here. Their names will lack the extra "C".

// We don't need to add these to ext_read_CSR() or ext_write_CSR() since those
// functions are for XLEN reads/writes which will never go through the non-CHERI
// handle_csr_op().

function clause is_CSR_defined(0x416) = cheri_registers_enabled() // ddc
function clause is_CSR_defined(0x780) = haveZstid() // mtid
function clause is_CSR_defined(0x580) = haveZstid() // stid
function clause is_CSR_defined(0x480) = haveZstid() // utid
function clause is_CSR_defined(0x7bc) = cheri_registers_enabled() & debug_mode_active // dddc
function clause is_CSR_defined(0x7bd) = cheri_registers_enabled() & debug_mode_active // dinfc


mapping clause csr_name_map = 0x416 <-> "ddc"
mapping clause csr_name_map = 0x780 <-> "mtid"
mapping clause csr_name_map = 0x580 <-> "stid"
mapping clause csr_name_map = 0x480 <-> "utid"
mapping clause csr_name_map = 0x7bc <-> "dddc"
mapping clause csr_name_map = 0x7bd <-> "dinfc"
