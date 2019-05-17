open ImpPrelude
open HConsingDefs

exception Stop;;
    
let xhCons (type a) (hh:a hashH) =
  let module MyHashedType = struct
    type t = a hashinfo
    let equal x y = hh.hash_eq x.hdata y.hdata
    let hash x = Hashtbl.hash x.hcodes 
  end in
  let module MyHashtbl = Hashtbl.Make(MyHashedType) in
  let pick t =
    let res = ref None in
    try
      MyHashtbl.iter (fun k d -> res:=Some (k,d); raise Stop) t;
      None
    with
    | Stop -> !res  
    in
  let t = MyHashtbl.create 1000 in
  let logs = ref [] in
  {
   hC = (fun (x:a hashinfo) ->
     match MyHashtbl.find_opt t x with
     | Some x' -> x'
     | None -> (*print_string "+";*)
        let x' = hh.set_hid x.hdata (MyHashtbl.length t) in
        MyHashtbl.add t x x'; x');
   next_log = (fun info -> logs := (MyHashtbl.length t, info)::(!logs));
   next_hid = (fun () -> MyHashtbl.length t);
   remove = (fun (x:a hashinfo) -> MyHashtbl.remove t x);
   export = fun () ->
     match pick t with
     | None -> { get_info = (fun _ -> raise Not_found);  iterall = (fun _ -> ()) } 
     | Some (k,_) ->
        (* the state is fully copied at export ! *)
        let logs = ref (List.rev_append (!logs) []) in
        let rec step_log i =
          match !logs with
          | (j, info)::l' when i>=j -> logs:=l'; info::(step_log i)
          | _ -> []
        in let a = Array.make (MyHashtbl.length t) k in
           MyHashtbl.iter (fun k d -> a.(hh.get_hid d) <- k) t;
           {
             get_info = (fun i -> a.(i));
             iterall = (fun iter_node -> Array.iteri (fun i k -> iter_node (step_log i) i k) a)
           }    
  }
