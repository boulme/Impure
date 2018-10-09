open ImpPrelude
open Datatypes

(** GENERIC ITERATIVE LOOP **) 

(* a simple version of loop *)
let simple_loop: ('a * ('a -> ('a, 'b) sum)) -> 'b
  = fun (a0, f) ->
    let rec iter: 'a -> 'b
      = fun a ->
        match f a with
        | Coq_inl a' -> iter a'
        | Coq_inr b -> b
    in
    iter a0;;

(* loop from while *)
let while_loop: ('a * ('a -> ('a, 'b) sum)) -> 'b
  = fun (a0, f) ->
    let s = ref (f a0) in
    while (match !s with Coq_inl _ -> true | _ -> false) do
      match !s with
      | Coq_inl a -> s:=f a
      | _ -> assert false
    done;
    match !s with
    | Coq_inr b -> b
    | _ -> assert false;;

let loop = simple_loop


(** GENERIC FIXPOINTS **)
  
let std_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b =
  let rec f x = recf f x in
  f

let memo_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b  =
  let memo = Hashtbl.create 10 in
  let rec f x =
    try
      Hashtbl.find memo x
    with
      Not_found ->
        let r = recf f x in
        Hashtbl.replace memo x r;
        r
  in f

let bare_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b  =
  let fix = ref (fun x -> failwith "init") in
  fix := (fun x -> recf !fix x);
  !fix;;
  
let buggy_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b =
  let memo = ref None in
  let rec f x =
    match !memo with
    | Some y -> y
    | None ->
       let r = recf f x in
       memo := Some r;
       r
  in f

let xrec_mode = ref MemoRec

let xrec_set_option : recMode -> unit
= fun m -> xrec_mode := m

let xrec : (('a -> 'b ) -> 'a -> 'b ) -> ('a -> 'b )
  = fun recf ->
    match !xrec_mode with
    | StdRec -> std_rec recf
    | MemoRec -> memo_rec recf
    | BareRec -> bare_rec recf
    | BuggyRec -> buggy_rec recf
