open ImpPrelude


(* 
Memoized version of translation from int -> BinNums.positive. 
The first arg is an indicative bound on the max int translated:
it pre-computes all positives lower or equal to this bound.  
*)
val memo_int2pos: int -> int -> BinNums.positive

val read_line: unit -> pstring

val print: pstring -> unit

val println: pstring -> unit

val string_of_Z: BinNums.coq_Z -> pstring

val timer : (('a -> 'b ) * 'a) -> 'b   

val new_exit_observer: (unit -> unit) -> (unit -> unit) ref

val set_exit_observer: (unit -> unit) ref * (unit -> unit) -> unit

val exn2string: exn -> pstring

val fail: pstring -> 'a

exception ImpureFail of pstring;;

val try_with_fail: (unit -> 'a) * (pstring -> exn -> 'a) -> 'a

val try_with_any: (unit -> 'a) * (exn -> 'a) -> 'a
