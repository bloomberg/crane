(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

let read_off ~settled params body =
  let n = List.length params in
  List.map2
    (fun (escapes, parts_escape) (_, ty) -> escapes || (parts_escape && Type_util.is_prod_ml_type ty))
    (List.combine
       (Escape.infer_owned_params ~callee_flags:settled n body)
       (Escape.infer_sub_bindings_escape_params n body))
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
      | Core.Decl.Value {entity = r; body = b; type_ = ty} when Type_util.ml_domains ty <> [] -> add r b ty
      | Core.Decl.Recursive_group fds ->
        Core.Nonempty.iter (fun (fd : Core.Recursion.Definition.t) -> add fd.entity fd.body fd.type_) fds
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
  (* Each round reads its callees' flags as the rounds before it left
     them. *)
  let flags = ref Ref.User.Map.empty in
  let settled r = Ref.User.Map.find_opt r !flags in
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, ty) ->
        let params, body = Type_util.declared_parameters ty b in
        let f = unless_receiver r (Table.with_decl_ref r (fun () -> read_off ~settled params body)) in
        if Ref.User.Map.find_opt r !flags <> Some f then (
          changed := true;
          flags := Ref.User.Map.add r f !flags ))
      fns;
    if !changed then round ()
  in
  round ();
  Ref.User.Map.bindings !flags

