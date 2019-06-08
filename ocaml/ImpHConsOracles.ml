open ImpPrelude
open HConsingDefs

let make_dict (type key) (p: key Dict.hash_params) =
  let module MyHashedType = struct
    type t = key
    let equal = p.Dict.test_eq 
    let hash = p.Dict.hashing 
  end in
  let module MyHashtbl = Hashtbl.Make(MyHashedType) in
  let dict = MyHashtbl.create 1000 in
  {
    Dict.set = (fun (k,d) -> MyHashtbl.replace dict k d);
    Dict.get = (fun k -> MyHashtbl.find_opt dict k)
  }


exception Stop;;

let xhCons (type a) (hp:a hashP) =
  (* We use a hash-table, but a hash-set would be sufficient !                    *)
  (* Thus, we could use a weak hash-set, but prefer avoid it for easier debugging *)
  (* Ideally, a parameter would allow to select between the weak or full version  *)
  let module MyHashedType = struct
    type t = a hashinfo
    let equal x y = hp.hash_eq x.hdata y.hdata
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
   hC = (fun (k:a hashinfo) ->
     match MyHashtbl.find_opt t k with
     | Some d -> d
     | None -> (*print_string "+";*)
        let d = hp.set_hid k.hdata (MyHashtbl.length t) in
        MyHashtbl.add t {k with hdata = d } d; d);
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
           MyHashtbl.iter (fun k d -> a.(hp.get_hid d) <- k) t;
           {
             get_info = (fun i -> a.(i));
             iterall = (fun iter_node -> Array.iteri (fun i k -> iter_node (step_log i) i k) a)
           }    
  }
