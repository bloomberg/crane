(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

let flags : bool list Ref.User.Map.t ref = State.cell State.Extraction Ref.User.Map.empty

let () = Escape.callee_flags := fun r -> Ref.User.Map.find_opt r !flags

let read_off params body =
  let n = List.length params in
  List.map2
    (fun (escapes, parts_escape) (_, ty) -> escapes || (parts_escape && Ml_type_util.is_prod_ml_type ty))
    (List.combine (Escape.infer_owned_params n body) (Escape.infer_sub_bindings_escape_params n body))
    params

(* Every function [struc] defines, in a functor or not, with its body and
   type: a constant with a parameter, and each member of a recursive group.
   A custom constant is not generated from its body: what it does with its
   arguments is its mapping's, which a call to it spells. *)
let functions struc =
  let acc = ref [] in
  let add r b ty = if not (Table.is_custom r) then acc := (r, b, ty) :: !acc in
  Modutil.struct_iter
    (function
      | Miniml.Dterm (r, b, ty) when Ml_type_util.ml_domains ty <> [] -> add r b ty
      | Miniml.Dfix fds -> List.iter (fun (fd : Miniml.ml_fix_def) -> add fd.fd_ref fd.fd_body fd.fd_type) fds
      | _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  List.rev !acc

let summarize ?(receiver = fun _ -> None) struc =
  let fns = functions struc in
  (* A method takes its receiver as the const [this], whatever its body does
     with it: a call hands it nothing to keep.  [receiver] counts parameters
     outermost first, the flags innermost first. *)
  let unless_receiver r flags =
    let n = List.length flags in
    List.mapi (fun i owned -> owned && receiver r <> Some (n - 1 - i)) flags
  in
  (* The fixed point is computed apart from the installed flags, which
     {!Escape} reads in the meantime as each round leaves them. *)
  let installed = !flags in
  flags := Ref.User.Map.empty;
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, ty) ->
        let params, body = Ml_type_util.declared_parameters ty b in
        let f = unless_receiver r (read_off params body) in
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

