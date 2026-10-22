(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

let flags : bool list Ref.User.Map.t ref = State.cell State.Extraction Ref.User.Map.empty

let () = Escape.callee_flags := fun r -> Ref.User.Map.find_opt r !flags

let summarize struc =
  let fns = Modutil.struct_functions struc in
  (* The fixed point is computed apart from the installed flags, which
     {!Escape} reads in the meantime as each round leaves them. *)
  let installed = !flags in
  flags := Ref.User.Map.empty;
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, _) ->
        let params, body = Mlutil.collect_lams b in
        let f = Escape.infer_owned_params (List.length params) body in
        if Ref.User.Map.find_opt r !flags <> Some f then (
          changed := true;
          flags := Ref.User.Map.add r f !flags ))
      fns;
    if !changed then round ()
  in
  round ();
  let summary = Ref.User.Map.bindings !flags in
  flags := installed;
  summary

let settled r = Ref.User.Map.find_opt r !flags

let install summary =
  flags := List.fold_left (fun m (r, f) -> Ref.User.Map.add r f m) Ref.User.Map.empty summary

