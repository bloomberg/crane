(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

open Miniml

let flags : bool list Table.Refmap'.t ref = State.cell State.Extraction Table.Refmap'.empty

let () = Escape.callee_flags := fun r -> Table.Refmap'.find_opt r !flags

let callables : (ml_type list * Escape.IntSet.t) Table.Refmap'.t ref =
  State.cell State.Extraction Table.Refmap'.empty

(* Every function of the structure: its name, body and type. *)
let functions struc =
  let acc = ref [] in
  let rec elems l =
    List.iter
      (fun (_, se) ->
        match se with
        | SEdecl (Dterm (r, (MLlam _ as b), ty)) -> acc := (r, b, ty) :: !acc
        | SEdecl (Dfix fds) ->
          List.iter (fun fd -> acc := (fd.fd_ref, fd.fd_body, fd.fd_type) :: !acc) fds
        | SEmodule {ml_mod_expr = MEstruct (_, l); _} -> elems l
        | _ -> ())
      l
  in
  List.iter (fun (_, l) -> elems l) struc;
  List.rev !acc

let settle struc =
  let fns = functions struc in
  flags := Table.Refmap'.empty;
  (* Which callables are generalised is each function's own business: one
     pass, the question {!Gen_functions.gen_dfun} asks of the same body. *)
  callables :=
    List.fold_left
      (fun m (r, b, ty) ->
        let ids, _ = Translation_support.collect_typed_lams ty b in
        Table.Refmap'.add r
          ( List.rev_map snd ids,
            Translation_support.ungeneralised_callables_of_definition r ty b )
          m )
      Table.Refmap'.empty fns;
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, _) ->
        let params, body = Mlutil.collect_lams b in
        let f = Escape.infer_owned_params (List.length params) body in
        if Table.Refmap'.find_opt r !flags <> Some f then (
          changed := true;
          flags := Table.Refmap'.add r f !flags ))
      fns;
    if !changed then round ()
  in
  round ()

let generalises_callable r pos ~primary f =
  match Table.Refmap'.find_opt r !callables with
  | Some (binder_tys, ungeneralised) -> (
    match Param_pos.source_index binder_tys pos with
    | Some i -> Translation_support.generalises_callable ~ungeneralised ~primary i f
    | None -> false )
  | None -> false
