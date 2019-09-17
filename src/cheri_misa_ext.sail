/* Veto disabling C if PCC.base is not 4-byte aligned 
   (assuming it is already 2-byte aligned) */
function ext_veto_disable_C () = getCapBaseBits(PCC)[1] == bitone

