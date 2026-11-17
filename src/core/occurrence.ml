(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A ref compares and hashes by its contents, which every occurrence shares,
   and is told apart from another only physically.  The contents are [0]
   except while [shared] counts visits in them, which is what lets it find a
   repeated occurrence in one pass, with no hash to go by. *)
type t = int ref

let fresh () = ref 0
let equal = ( == )

let shared iter =
  let found = ref [] in
  let visit o =
    match !o with
    | 0 -> o := 1
    | 1 -> o := 2; found := o :: !found
    | _ -> ()
  in
  Fun.protect ~finally:(fun () -> iter (fun o -> o := 0)) (fun () -> iter visit; List.rev !found)
