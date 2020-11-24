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
// XXX: the following appears to trigger a C code generator bug:
// error: implicit declaration of function 'hex_bits_5_matches_prefix' is invalid in C99
// mapping clause scr_name_map = screg   <-> hex_bits_5(screg)
mapping clause scr_name_map = 0b00010 <-> "0x2"
mapping clause scr_name_map = 0b00011 <-> "0x3"
mapping clause scr_name_map = 0b01000 <-> "0x8"
mapping clause scr_name_map = 0b01001 <-> "0x9"
mapping clause scr_name_map = 0b01010 <-> "0xA"
mapping clause scr_name_map = 0b01011 <-> "0xB"
mapping clause scr_name_map = 0b01100 <-> "0xC"
mapping clause scr_name_map = 0b01101 <-> "0xD"
mapping clause scr_name_map = 0b01110 <-> "0xE"
mapping clause scr_name_map = 0b01111 <-> "0xF"
mapping clause scr_name_map = 0b10000 <-> "0x10"
mapping clause scr_name_map = 0b10001 <-> "0x11"
mapping clause scr_name_map = 0b10010 <-> "0x12"
mapping clause scr_name_map = 0b10011 <-> "0x13"
mapping clause scr_name_map = 0b11000 <-> "0x18"
mapping clause scr_name_map = 0b11001 <-> "0x19"
mapping clause scr_name_map = 0b11010 <-> "0x1A"
mapping clause scr_name_map = 0b11011 <-> "0x1B"

val scr_name : screg -> string
overload to_str = {scr_name}
