include Platform_uncurried
let read_mem rk addrsize addr len = read_mem (rk, addrsize, addr, len)
let write_mem wk addrsize addr len value = write_mem (wk, addrsize, addr, len, value)
let write_mem_ea wk addrsize addr len = write_mem_ea (wk, addrsize, addr, len)
