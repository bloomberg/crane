(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a relaxation of a function's head decided, as data.  See
    [head_relaxation.mli]. *)

open Names
open Minicpp

type t =
  | Computed_return of cpp_type
  | Param_applications of {
      relaxed : Id.t list;
      deduced : ((Id.t * cpp_type list) * Id.t) list;
    }
  | Deapplied of {
      plain : Id.t list;
      in_scope : Id.t list;
    }
  | Unmentioned of Id.t list

let equal = ( = )

(* {!Param_applications}'s rewrite of one type: an application of a
   [relaxed] variable is replaced by the parameter [deduced] names for it. *)
let param_applications relaxed deduced =
  let key t =
    match t with
    | Tapply (h, args) -> (
      match List.find_opt (fun id -> tvar_is id h) relaxed with
      | Some id -> Some (id, args)
      | None -> None )
    | _ -> None
  in
  map_cpp_type (fun t ->
      match Option.bind (key t) (fun k -> List.assoc_opt k deduced) with
      | Some id -> Tvar (Tv_named id)
      | None -> t )

let deapplied ~plain ~in_scope =
  let rec ft t =
    map_cpp_type
      (function
        | Tapply (head, args) when List.exists (fun id -> tvar_is id head) plain -> (
          (* Named as it is declared: a head converted without names is
             otherwise spelled [std::any]. *)
          let head =
            match head with
            | Tvar (Tv_index (i, None)) ->
              Tvar (Tv_index (i, List.find_opt (fun id -> tvar_is id head) plain))
            | _ -> head
          in
          Minicpp.rebind_plain_var ~in_scope head args )
        (* A carrier abstraction's body is written too, through a holder;
           [map_cpp_type] leaves it alone. *)
        | Ttyctor body -> Ttyctor (ft body)
        | t -> t )
      t
  in
  ft

(* {!Unmentioned}'s rewrite of one type: a variable among [ids], applied or
   not, becomes [std::any]. *)
let unmentioned_erased ids =
  (* Stricter than {!Minicpp.tvar_is}, which lets an unresolved head answer to its
     index as well as to its name: a relaxation names its parameters [F1],
     [_P0] without renumbering them, so a variable that kept index 1 would
     otherwise answer for [T1]. *)
  let is_tvar id = function
    | Tvar (Tv_index (_, Some n) | Tv_named n) -> Id.equal n id
    | Tvar (Tv_index (i, None)) -> Id.equal (tvar_id i) id
    | _ -> false
  in
  let is_unmentioned t =
    let head = match t with Ttyctor h | Tapply (h, _) -> h | h -> h in
    List.exists (fun id -> is_tvar id head) ids
  in
  map_cpp_type (fun t -> if is_unmentioned t then Tany else t)

let apply relaxation decl =
  match relaxation with
  | Computed_return ret -> ( match decl with Dfun f -> Dfun {f with df_ret = ret} | d -> d )
  | Param_applications {relaxed; deduced} -> (
    (* The body annotates the very types the parameters do -- a pattern match
       names the scrutinee's constructor struct -- so a relaxation that
       renames a parameter's type has to rename the body's too, or the body
       goes on applying a variable the signature no longer declares as a
       template.  The return type is left alone. *)
    let ft = param_applications relaxed deduced in
    match decl with
    | Dfun ({df_shape = Ddef (params, body); _} as f) ->
      let rec fe e = Minicpp.map_expr fe fs ft e
      and fs st = Minicpp.map_stmt fe fs ft st in
      Dfun {f with df_shape = Ddef (List.map (fun (n, ty) -> (n, ft ty)) params, List.map fs body)}
    | d -> d )
  | Deapplied {plain; in_scope} -> (
    let ft = deapplied ~plain ~in_scope in
    (* A lambda whose parameter deduced a template parameter only through the
       application just taken off no longer does. *)
    let settle = function
      | CPPlambda l -> CPPlambda (Minicpp.settle_lambda_tparams l)
      | e -> e
    in
    let rec fe e = settle (Minicpp.map_expr fe fs ft e)
    and fs st = Minicpp.map_stmt fe fs ft st in
    match decl with
    | Dfun ({df_ret = ret; df_shape = Ddef (params, body); _} as f) ->
      Dfun
        { f with
          df_ret = ft ret;
          df_shape = Ddef (List.map (fun (n, ty) -> (n, ft ty)) params, List.map fs body) }
    | Dfun ({df_ret = ret; df_shape = Ddecl params; _} as f) ->
      Dfun {f with df_ret = ft ret; df_shape = Ddecl (List.map (fun (n, ty) -> (n, ft ty)) params)}
    | Dasgn a -> Dasgn {a with da_type = ft a.da_type; da_init = fe a.da_init}
    | Dstruct _ | Dnspace _ | Dtemplate _ ->
      (* An inductive's own fields and members, for the same reason: a family
         parameter left plain is applied in its payloads. *)
      Minicpp.map_decl fe fs ft decl
    | _ -> decl )
  | Unmentioned ids -> (
    let erase = unmentioned_erased ids in
    let erase_params l = List.map (fun (id, t) -> (id, erase t)) l in
    match decl with
    | Dfun ({df_shape; _} as f) ->
      let df_shape =
        match df_shape with
        | Ddef (params, body) ->
          let rec fe e =
            match e with
            (* The cast's target is left alone; its operand is not. *)
            | CPPany_cast (ty, e') -> CPPany_cast (ty, fe e')
            | CPPany_cast_tolerant (ty, e') -> CPPany_cast_tolerant (ty, fe e')
            | e -> Minicpp.map_expr fe fs erase e
          and fs s = Minicpp.map_stmt fe fs erase s in
          Ddef (erase_params params, List.map fs body)
        | Ddecl params -> Ddecl (erase_params params)
      in
      Dfun {f with df_ret = erase f.df_ret; df_shape}
    | d -> d )

let apply_all relaxations decl = List.fold_left (fun d r -> apply r d) decl relaxations

(* The CppIR counterparts of the [Deapplied] rewrite, for a generated struct
   that is already CppIR. *)

module L = Cpp_ir.Lowered

(* {!Minicpp.tvar_is}: a variable answers to its parameter's name and to the
   spelling of its index. *)
let lowered_tvar_is id : L.Type.t -> bool = function
  | Variable (Named n) -> Id.equal n id
  | Variable (Index (i, name)) ->
    (match name with Some n -> Id.equal n id | None -> false) || Id.equal (tvar_id i) id
  | _ -> false

(* {!Minicpp.tvar_name}. *)
let lowered_tvar_name : L.Type.t -> Id.t option = function
  | Variable (Index (_, Some n) | Named n) -> Some n
  | Variable (Index (i, None)) -> Some (tvar_id i)
  | _ -> None

(* {!Minicpp.rebind_plain_var}. *)
let lowered_rebind_plain_var ~in_scope (head : L.Type.t) (args : L.Type.t list) : L.Type.t =
  match args with
  | [a] when not (Cpp_ir.Types.prints_as_any a) ->
    let names = ref [] in
    ignore
      (Cpp_ir.Children.exists_type
         (fun t ->
           Option.iter (fun n -> names := n :: !names) (lowered_tvar_name t);
           false )
         a );
    if List.for_all (fun n -> List.exists (Id.equal n) in_scope) !names then Rebind (head, a) else head
  | _ -> head

(* {!deapplied} over a CppIR type. *)
let deapplied_lowered ~plain ~in_scope =
  let rec ft t =
    Cpp_ir.Types.map
      (fun (t : L.Type.t) : L.Type.t ->
        match t with
        | Apply (head, args) when List.exists (fun id -> lowered_tvar_is id head) plain ->
          let head : L.Type.t =
            match head with
            | Variable (Index (i, None)) ->
              Variable (Index (i, List.find_opt (fun id -> lowered_tvar_is id head) plain))
            | _ -> head
          in
          lowered_rebind_plain_var ~in_scope head args
        | Type_constructor body -> Type_constructor (ft body)
        | t -> t )
      t
  in
  ft

(* A rewrite of every expression, statement and type under it, bottom-up,
   [fe] applied to each rebuilt expression. *)
let lowered_deep ?(fe = Fun.id) (ft : L.Type.t -> L.Type.t) =
  let rec m () = Cpp_ir.Map.make ~expr ~stmt ~type_:ft ()
  and expr e = fe (Cpp_ir.Map.expr (m ()) e)
  and stmt s = Cpp_ir.Map.stmt (m ()) s in
  m ()

(* {!Minicpp.settle_lambda_tparams}: [l] without the template parameters
   none of its parameters names, each use of them erased. *)
let settle_lowered_lambda (l : L.phase Cpp_ir.Expr.Lambda.t) =
  let names id t = Cpp_ir.Children.exists_type (lowered_tvar_is id) t in
  match List.filter (fun x -> not (List.exists (fun (t, _) -> names x t) l.params)) l.type_params with
  | [] -> l
  | ids ->
    let ft = Cpp_ir.Types.map (fun t -> if List.exists (fun id -> lowered_tvar_is id t) ids then Any else t) in
    let kept = List.filter (fun x -> not (List.exists (Id.equal x) ids)) l.type_params in
    {(Cpp_ir.Map.lambda (lowered_deep ft) l) with type_params = kept}

let deapply_struct ~plain ~in_scope (d : L.Decl.t) : L.Decl.t =
  let fe : L.Expr.t -> L.Expr.t = function Lambda l -> Lambda (settle_lowered_lambda l) | e -> e in
  Cpp_ir.Map.decl (lowered_deep ~fe (deapplied_lowered ~plain ~in_scope)) d
