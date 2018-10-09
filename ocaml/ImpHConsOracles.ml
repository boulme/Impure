open ImpPrelude

exception Stop;;
    
let xhCons (type a) (hash_eq, error: (a -> a -> bool)*(a pre_hashV -> a hashV)) =
  let module MyHashedType = struct
    type t = a pre_hashV
    let equal x y = hash_eq x.pre_data y.pre_data
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
   hC = (fun (x:a pre_hashV) ->
     match MyHashtbl.find_opt t x with
     | Some x' -> x'
     | None -> (*print_string "+";*)
        let x' = { data = x.pre_data ;
                   hid = MyHashtbl.length t }
        in MyHashtbl.add t x x'; x');
   hC_known = (fun (x:a pre_hashV) ->
     match MyHashtbl.find_opt t x with
     | Some x' -> x'
     | None -> error x);
   next_log = (fun info -> logs := (MyHashtbl.length t, info)::(!logs));
   export = fun () ->
     match pick t with
     | None -> { get_hashV = (fun _ -> raise Not_found);  iterall = (fun _ -> ()) } 
     | Some (k,_) ->
        (* the state is fully copied at export ! *)
        let logs = ref (List.rev_append (!logs) []) in
        let rec step_log i =
          match !logs with
          | (j, info)::l' when i>=j -> logs:=l'; info::(step_log i)
          | _ -> []
        in let a = Array.make (MyHashtbl.length t) k in
           MyHashtbl.iter (fun k d -> a.(d.hid) <- k) t;
           {
             get_hashV = (fun i -> a.(i));
             iterall = (fun iter_node -> Array.iteri (fun i k -> iter_node (step_log i) i k) a)
           }    
  }
