/* CHERI specific helpers */

val MEMr_tag = "read_tag_bool"  : bits(64) -> bool effect { rmemt }
val MEMw_tag = "write_tag_bool" : (bits(64) , bool) -> unit effect { wmvt }

val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1) effect pure
function MAX(n) = pow2(n) - 1

val not = {coq:"negb", _:"not"} : bool -> bool

val CountLeadingZeros = {c: "count_leading_zeros", smt:"count_leading_zeros"} : forall 'N , 'N >= 2. bits('N) -> {'n, 0 <= 'n <= 'N . atom('n)}
function CountLeadingZeros x = {
  foreach (i from ('N - 1) to 0 by 1 in dec)
    if [x[i]] == 0b1 then return 'N - i - 1;
  return 'N;
}
