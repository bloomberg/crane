(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

open Miniml

let flags : bool list Table.Refmap'.t ref = State.cell State.Extraction Table.Refmap'.empty

let () = Escape.callee_flags := fun r -> Table.Refmap'.find_opt r !flags

(* Every function of the structure: its name and body. *)
let functions struc =
  let acc = ref [] in
  let rec elems l =
    List.iter
      (fun (_, se) ->
        match se with
        | SEdecl (Dterm (r, (MLlam _ as b), _)) -> acc := (r, b) :: !acc
        | SEdecl (Dfix fds) -> List.iter (fun fd -> acc := (fd.fd_ref, fd.fd_body) :: !acc) fds
        | SEmodule {ml_mod_expr = MEstruct (_, l); _} -> elems l
        | _ -> ())
      l
  in
  List.iter (fun (_, l) -> elems l) struc;
  List.rev !acc

let settle struc =
  let fns = functions struc in
  flags := Table.Refmap'.empty;
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b) ->
        let params, body = Mlutil.collect_lams b in
        let f = Escape.infer_owned_params (List.length params) body in
        if Table.Refmap'.find_opt r !flags <> Some f then (
          changed := true;
          flags := Table.Refmap'.add r f !flags ))
      fns;
    if !changed then round ()
  in
  round ()
