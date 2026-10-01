(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A coinductive's field projection hands out a reference.  See
    [borrow_projection.mli]. *)

open Names
open Minicpp

let rec reads_this e =
  match e with
  | CPPthis -> true
  | _ ->
    let found = ref false in
    iter_expr_children
      ~on_expr:(fun e -> if reads_this e then found := true)
      ~on_stmts:(fun _ -> ())
      e;
    !found

(* [m] reads one field of its own receiver and returns it: a single-branch
   match on [this], borrowed, whose body returns one of the fields it
   binds. *)
let is_projection m =
  (not m.mf_is_static) && m.mf_is_const && m.mf_params = []
  && m.mf_ref_qual = Rq_any && (not m.mf_is_conversion)
  && ( match m.mf_ret_type with
     | Tref _ | Tvoid -> false
     | _ -> true )
  &&
  match m.mf_body with
  | [Smatch (sc, [b], None)] ->
    (not sc.sc_owned) && b.smb_extra_conds = [] && reads_this sc.sc_expr
    &&
    ( match b.smb_body with
    | [Sreturn (Some (CPPvar x))] ->
      List.exists (fun (y, _, _) -> Id.equal x y) b.smb_field_bindings
    | _ -> false )
  | _ -> false

(* The projection as the pair that cannot dangle: a reference for an lvalue
   receiver, and a copy for a temporary one, which dies at the end of the
   full expression that called it. *)
let split m =
  [ Fmethod {m with mf_ret_type = Tref (Lvalue, Tconst m.mf_ret_type); mf_ref_qual = Rq_lvalue};
    Fmethod {m with mf_ref_qual = Rq_rvalue} ]

let fields fs =
  List.concat_map
    (fun (f, vis, tag) ->
      match f with
      | Fmethod m when is_projection m ->
        List.map (fun f -> (f, vis, tag)) (split m)
      | _ -> [(f, vis, tag)] )
    fs

let rec transform_decl d =
  match d with
  | Dtemplate (tps, c, inner) -> Dtemplate (tps, c, transform_decl inner)
  | Dnspace (r, ds) -> Dnspace (r, List.map transform_decl ds)
  | Dstruct s when Table.is_coinductive s.ds_ref ->
    Dstruct {s with ds_fields = fields s.ds_fields}
  | d -> d
