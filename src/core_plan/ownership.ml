(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Parameter ownership settled across calls.  See [ownership.mli]. *)

let read_off ?matches_reuse ~settled params body =
  let n = List.length params in
  List.map2
    (fun (escapes, parts_escape) (_, ty) -> escapes || (parts_escape && Base.Type_util.is_prod_core_type ty))
    (List.combine
       (Escape.infer_owned_params ?matches_reuse ~callee_flags:settled n body)
       (Escape.infer_sub_bindings_escape_params n body))
    params

(* Every function [struc] defines, in a functor or not, with its body and
   type: a constant with a parameter, and each member of a recursive group.
   A custom constant is not generated from its body: what it does with its
   arguments is its mapping's, which a call to it spells. *)
let functions struc =
  let acc = ref [] in
  let add ~value r b ty = if not (Base.Table.is_custom r) then acc := (r, b, ty, value) :: !acc in
  Core_passes.Modutil.struct_iter
    (function
      | Core.Decl.Value {entity = r; body = b; type_ = ty} when Base.Type_util.core_domains ty <> [] ->
        add ~value:true r b ty
      | Core.Decl.Recursive_group fds ->
        Core.Nonempty.iter (fun (fd : Core.Recursion.Definition.t) -> add ~value:false fd.entity fd.body fd.type_) fds
      | _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    struc;
  List.rev !acc

(* Whether the matches of the function [r], a constant if [value], may
   reuse their scrutinee's cell: Loopify does not rewrite its body, because
   it is not loopified or has no recursion to loopify. *)
let matches_reuse ~value r body =
  Base.Table.with_decl_ref r Base.Table.reuse_loopify_ok || (value && Escape.loop_free body)

let reusing_matches struc =
  List.fold_left
    (fun s (r, b, _, value) -> if matches_reuse ~value r b then Core.Ref.User.Set.add r s else s)
    Core.Ref.User.Set.empty (functions struc)

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
  let flags = ref Core.Ref.User.Map.empty in
  let settled r = Core.Ref.User.Map.find_opt r !flags in
  (* Each round can only turn borrowed parameters owned, so it stops. *)
  let rec round () =
    let changed = ref false in
    List.iter
      (fun (r, b, ty, value) ->
        let params, body = Base.Type_util.declared_parameters ty b in
        let matches_reuse = matches_reuse ~value r b in
        let f =
          unless_receiver r (Base.Table.with_decl_ref r (fun () -> read_off ~matches_reuse ~settled params body))
        in
        if Core.Ref.User.Map.find_opt r !flags <> Some f then (
          changed := true;
          flags := Core.Ref.User.Map.add r f !flags ))
      fns;
    if !changed then round ()
  in
  round ();
  Core.Ref.User.Map.bindings !flags

