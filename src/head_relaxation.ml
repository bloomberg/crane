(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a relaxation of a function's head decided, as data.  See
    [head_relaxation.mli]. *)

open Names

type t =
  | Computed_return of Cpp_ir.Lowered.Type.t
  | Param_applications of {
      relaxed : Id.t list;
      deduced : ((Id.t * Cpp_ir.Lowered.Type.t list) * Id.t) list;
    }
  | Deapplied of {
      plain : Id.t list;
      in_scope : Id.t list;
    }
  | Unmentioned of Id.t list

let equal = ( = )

module L = Cpp_ir.Lowered

(* {!Minicpp.tvar_is}: a variable answers to its parameter's name and to the
   spelling of its index. *)
let lowered_tvar_is id : L.Type.t -> bool = function
  | Variable (Named n) -> Id.equal n id
  | Variable (Index (i, name)) ->
    (match name with Some n -> Id.equal n id | None -> false) || Id.equal (Common.tvar_id i) id
  | _ -> false

(* {!Minicpp.tvar_name}. *)
let lowered_tvar_name : L.Type.t -> Id.t option = function
  | Variable (Index (_, Some n) | Named n) -> Some n
  | Variable (Index (i, None)) -> Some (Common.tvar_id i)
  | _ -> None

(* {!Minicpp.rebind_plain_var}. *)
let rebind_plain_var_lowered ~in_scope (head : L.Type.t) (args : L.Type.t list) : L.Type.t =
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

(* {!Deapplied}'s rewrite of one type. *)
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
          rebind_plain_var_lowered ~in_scope head args
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

(* {!Param_applications}'s rewrite of one type: an application of a
   [relaxed] variable is replaced by the parameter [deduced] names for it. *)
let param_applications_lowered relaxed deduced =
  let key (t : L.Type.t) =
    match t with
    | Apply (h, args) -> (
      match List.find_opt (fun id -> lowered_tvar_is id h) relaxed with
      | Some id -> Some (id, args)
      | None -> None )
    | _ -> None
  in
  Cpp_ir.Types.map (fun t ->
      match Option.bind (key t) (fun k -> List.assoc_opt k deduced) with
      | Some id -> (Variable (Named id) : L.Type.t)
      | None -> t )

(* {!Unmentioned}'s rewrite of one type: a variable among [ids], applied or
   not, becomes [std::any].  Stricter than {!lowered_tvar_is}, which lets an
   unresolved head answer to its index as well as to its name: a relaxation
   names its parameters [F1], [_P0] without renumbering them, so a variable
   that kept index 1 would otherwise answer for [T1]. *)
let unmentioned_erased_lowered ids =
  let is_tvar id : L.Type.t -> bool = function
    | Variable (Index (_, Some n) | Named n) -> Id.equal n id
    | Variable (Index (i, None)) -> Id.equal (Common.tvar_id i) id
    | _ -> false
  in
  let is_unmentioned (t : L.Type.t) =
    let head = match t with Type_constructor h | Apply (h, _) -> h | h -> h in
    List.exists (fun id -> is_tvar id head) ids
  in
  Cpp_ir.Types.map (fun t -> if is_unmentioned t then (Any : L.Type.t) else t)

let apply_signature relaxation ~params ~ret =
  match relaxation with
  | Computed_return ret -> (params, ret)
  | Param_applications {relaxed; deduced} ->
    let ft = param_applications_lowered relaxed deduced in
    (List.map ft params, ret)
  | Deapplied {plain; in_scope} ->
    let ft = deapplied_lowered ~plain ~in_scope in
    (List.map ft params, ft ret)
  | Unmentioned ids ->
    let erase = unmentioned_erased_lowered ids in
    (List.map erase params, erase ret)

let deapply_struct ~plain ~in_scope (d : L.Decl.t) : L.Decl.t =
  let fe : L.Expr.t -> L.Expr.t = function Lambda l -> Lambda (settle_lowered_lambda l) | e -> e in
  Cpp_ir.Map.decl (lowered_deep ~fe (deapplied_lowered ~plain ~in_scope)) d

let apply relaxation (decl : L.Decl.t) : L.Decl.t =
  match relaxation with
  | Computed_return ret -> ( match decl with Function f -> Function {f with return_type = ret} | d -> d )
  | Param_applications {relaxed; deduced} -> (
    (* The body annotates the very types the parameters do -- a pattern match
       names the scrutinee's constructor struct -- so a relaxation that
       renames a parameter's type has to rename the body's too, or the body
       goes on applying a variable the signature no longer declares as a
       template.  The return type is left alone. *)
    let ft = param_applications_lowered relaxed deduced in
    match decl with
    | Function ({shape = Definition (params, body); _} as f) ->
      let m = lowered_deep ft in
      Function
        {f with shape = Definition (List.map (fun (n, ty) -> (n, ft ty)) params, List.map (Cpp_ir.Map.stmt m) body)}
    | d -> d )
  | Deapplied {plain; in_scope} -> (
    let ft = deapplied_lowered ~plain ~in_scope in
    (* A lambda whose parameter deduced a template parameter only through the
       application just taken off no longer does. *)
    let fe : L.Expr.t -> L.Expr.t = function Lambda l -> Lambda (settle_lowered_lambda l) | e -> e in
    let m = lowered_deep ~fe ft in
    match decl with
    | Function ({shape = Definition (params, body); _} as f) ->
      Function
        { f with
          return_type = ft f.return_type;
          shape = Definition (List.map (fun (n, ty) -> (n, ft ty)) params, List.map (Cpp_ir.Map.stmt m) body) }
    | Function ({shape = Declaration params; _} as f) ->
      Function
        {f with return_type = ft f.return_type; shape = Declaration (List.map (fun (n, ty) -> (n, ft ty)) params)}
    | Variable v -> Variable {v with type_ = ft v.type_; init = m.expr v.init}
    | Struct _ | Namespace _ | Template _ ->
      (* An inductive's own fields and members, for the same reason: a family
         parameter left plain is applied in its payloads. *)
      Cpp_ir.Map.decl m decl
    | _ -> decl )
  | Unmentioned ids -> (
    let erase = unmentioned_erased_lowered ids in
    let erase_params l = List.map (fun (id, t) -> (id, erase t)) l in
    match decl with
    | Function f ->
      let shape : L.phase Cpp_ir.Function.shape =
        match f.shape with
        | Definition (params, body) ->
          let rec fe (e : L.Expr.t) : L.Expr.t =
            match e with
            (* The cast's target is left alone; its operand is not. *)
            | Any_cast (ty, e') -> Any_cast (ty, fe e')
            | Tolerant_any_cast (ty, e') -> Tolerant_any_cast (ty, fe e')
            | e -> Cpp_ir.Map.expr (m ()) e
          and fs s = Cpp_ir.Map.stmt (m ()) s
          and m () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:erase () in
          Definition (erase_params params, List.map fs body)
        | Declaration params -> Declaration (erase_params params)
      in
      Function {f with return_type = erase f.return_type; shape}
    | d -> d )

let apply_all relaxations decl = List.fold_left (fun d r -> apply r d) decl relaxations
