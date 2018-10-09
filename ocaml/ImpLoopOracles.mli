open ImpPrelude
open Datatypes

val loop: ('a * ('a -> ('a, 'b) sum)) -> 'b

val xrec_set_option: recMode -> unit 

val xrec: (('a -> 'b ) -> 'a -> 'b ) -> ('a -> 'b ) 
