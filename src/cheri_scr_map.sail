/* Mapping of scr addresses to their names. */

val scr_name_map : screg <-> string

scattered mapping scr_name_map

mapping clause scr_name_map = 0b00000 <-> "pcc"
mapping clause scr_name_map = 0b00001 <-> "ddc"

mapping clause scr_name_map = 0b00100 <-> "utcc"
mapping clause scr_name_map = 0b00101 <-> "utdc"
mapping clause scr_name_map = 0b00110 <-> "uscratchc"
mapping clause scr_name_map = 0b00111 <-> "uepcc"

mapping clause scr_name_map = 0b10100 <-> "stcc"
mapping clause scr_name_map = 0b10101 <-> "stdc"
mapping clause scr_name_map = 0b10110 <-> "sscratchc"
mapping clause scr_name_map = 0b10111 <-> "sepcc"

mapping clause scr_name_map = 0b11100 <-> "mtcc"
mapping clause scr_name_map = 0b11101 <-> "mtdc"
mapping clause scr_name_map = 0b11110 <-> "mscratchc"
mapping clause scr_name_map = 0b11111 <-> "mepcc"

val scr_name : screg -> string
overload to_str = {scr_name}
