register dpcc       : Capability = null_cap
register dscratch0c : Capability = null_cap
register dscratch1c : Capability = null_cap
register dddc       : Capability = null_cap
register dinfc      : Capability = infinite_cap

function set_dpcc(value : Capability) -> unit = dpcc = legalize_epcc(convertInvalidAddr(value))
function set_dscratch0c(value : Capability) -> unit = dscratch0c = value
function set_dscratch1c(value : Capability) -> unit = dscratch1c = value
function set_dddc(value : Capability) -> unit = dddc = convertInvalidAddrCap(value)
function set_dinfc(value : Capability) -> unit = () // dinfc has no writable fields

function get_dinfc() -> Capability = dinfc

function set_dpc(value : xlenbits) -> xlenbits = {
  dpcc = setCapAddrChecked(dpcc, legalize_xepc(convertInvalidAddr(value)));
  dpcc.address
}
function set_dscratch0(value : xlenbits) -> xlenbits = {
  dscratch0c = setCapAddrChecked(dscratch0c, value);
  dscratch0c.address
}
function set_dscratch1(value : xlenbits) -> xlenbits = {
  dscratch1c = setCapAddrChecked(dscratch1c, value);
  dscratch1c.address
}

function set_dddc_xlen(value: xlenbits) -> xlenbits = {
  dddc = setCapAddrChecked(dddc, convertInvalidAddr(value));
  dddc.address
}

function set_dinfc_xlen(value : xlenbits) -> xlenbits = {
  // Perform no update since dinfc has no writable fields
  dinfc.address
}

function get_dpc() -> xlenbits = dpcc.address
function get_dscratch0() -> xlenbits = dscratch0c.address
function get_dscratch1() -> xlenbits = dscratch1c.address
