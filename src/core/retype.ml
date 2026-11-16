(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A term or program taken from one phase to another by mapping each of
    its annotations: what freezing a program does ({!Core_phase.freeze}),
    and what widening a frozen term does ({!Widen}).  The annotations are
    visited in the order {!Core_util.ast_map_types} and
    {!Modutil.map_struct} visit them, so a mapping with an effect -- minting
    an open annotation for each unsolved metavariable it meets -- has it in
    the same order. *)

open Grammar

(** [type_leaf t] is the node [t] itself at another phase, for a [t] whose
    payload does not mention the phase: a variable, a hole, an open
    annotation, an erased slot, [Unknown], [Axiom] or [String].  Freezing
    keeps such a node rather than copying it, as the in-place freezing it
    replaced did: {!Local_types} tells a minted variable apart by the node.
    Raises [Invalid_argument] for any other node. *)
let type_leaf : 'p Type.at -> 'q Type.at = function
  | (Type.Variable _ | Type.Hole _ | Type.Open _ | Type.Erased _ | Type.Unknown | Type.Axiom | Type.String) as t ->
    (* The representation of these constructors is the same at every phase. *)
    Obj.magic t
  | Type.Arrow _ | Type.Global_app _ | Type.Variable_app _ | Type.Meta _ -> invalid_arg "Core.Retype.type_leaf"

(* The node [e] itself at another phase, for a term with no subterm and no
   annotation, as {!type_leaf}. *)
let expr_leaf : 'p Expr.at -> 'q Expr.at = fun e -> Obj.magic e

(** [global_use f u] is [u] with [f] applied to every type of its
    instantiation. *)
let global_use f (u : _ Global_use.at) =
  match u.instance with
  | Global_use.Monomorphic -> Global_use.make u.callee Global_use.Monomorphic u.occurrence
  | Global_use.Polymorphic inst ->
    Global_use.make u.callee (Global_use.Polymorphic (Scheme.Instantiation.map f inst)) u.occurrence

(** [expr f e] is [e] with [f] applied to every annotation: binder types,
    the types of uses, constructions, matches, branches, coercions and local
    recursive groups. *)
let rec expr : ('p Type.at -> 'q Type.at) -> 'p Expr.at -> 'q Expr.at =
 fun f -> function
  | Expr.Lambda {parameter = i; parameter_type = t; body = a} ->
    Expr.Lambda {parameter = i; parameter_type = f t; body = expr f a}
  | Expr.Let {binder = i; binder_type = t; value = a; body = b; occurrence = occ} ->
    Expr.Let {binder = i; binder_type = f t; value = expr f a; body = expr f b; occurrence = occ}
  | Expr.Global use -> Expr.Global (global_use f use)
  | Expr.Construct {result_type = t; constructor = c; arguments = l; occurrence = occ} ->
    Expr.Construct {result_type = f t; constructor = c; arguments = List.map (expr f) l; occurrence = occ}
  | Expr.Tuple l -> Expr.Tuple (List.map (expr f) l)
  | Expr.Match {scrutinee_type = t; scrutinee = a; branches = v; occurrence = occ} ->
    let branch {Match.Branch.binders = binds; result_type = bty; pattern = pat; body} =
      { Match.Branch.binders = List.map (fun (id, bt) -> (id, f bt)) binds;
        result_type = f bty;
        pattern = pat;
        body = expr f body }
    in
    Expr.Match {scrutinee_type = f t; scrutinee = expr f a; branches = Array.map branch v; occurrence = occ}
  | Expr.Fixpoint g -> Expr.Fixpoint (group f g)
  | Expr.Cofixpoint g -> Expr.Cofixpoint (group f g)
  | Expr.Apply {callee = a; arguments = l} -> Expr.Apply {callee = expr f a; arguments = List.map (expr f) l}
  | Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Expr.Coerce {source_type = f from; target_type = f into; value = expr f a; occurrence = mocc}
  | Expr.Boxed_value {value = a; occurrence = mocc} -> Expr.Boxed_value {value = expr f a; occurrence = mocc}
  | Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Expr.Lambda_group_barrier {value = expr f a; occurrence = mocc}
  | Expr.Persistent_array {elements = t; default = def} ->
    Expr.Persistent_array {elements = Array.map (expr f) t; default = expr f def}
  | ( Expr.Bound_variable _
    | Expr.Runtime_error _
    | Expr.Erased_value _
    | Expr.Axiom_value _
    | Expr.UInt63 _ | Expr.Numeral _
    | Expr.Float64 _
    | Expr.String _ ) as a -> expr_leaf a

(* The bodies first, then the types, as {!Recursion.Group.map}. *)
and group f (g : _ Recursion.Group.at) =
  let bodies = Array.map (fun (m : _ Recursion.Member.at) -> expr f m.body) g.members in
  let types = Array.map (fun (m : _ Recursion.Member.at) -> f m.type_) g.members in
  Recursion.Group.make ~selected:g.selected
    (Array.mapi
       (fun i (m : _ Recursion.Member.at) -> {Recursion.Member.name = m.name; type_ = types.(i); body = bodies.(i)})
       g.members )
    g.occurrence

(** [program ~spec ~with_type decl s] is the program [s] with [decl] applied
    to every declaration, [spec] to every specification and [with_type] to
    the type each [with] refinement fixes. *)
let program ~spec ~with_type decl (s : (Names.ModPath.t * 'p Module_structure.at) list) =
  let rec mtype = function
    | Module_type.Path p -> Module_type.Path p
    | Module_type.Functor {parameter = mbid; parameter_type = mt; result = mt'} ->
      Module_type.Functor {parameter = mbid; parameter_type = mtype mt; result = mtype mt'}
    | Module_type.Signature {path = mp; items = sign} ->
      Module_type.Signature {path = mp; items = List.map (fun (l, s) -> (l, specif s)) sign}
    | Module_type.Refined
        {base = mt; refinement = Refinement.Type_equation {path = idl; parameters = l; definition = t}} ->
      Module_type.Refined
        {base = mtype mt; refinement = Refinement.Type_equation {path = idl; parameters = l; definition = with_type t}}
    | Module_type.Refined {base = mt; refinement = Refinement.Module_equation {path; definition}} ->
      Module_type.Refined {base = mtype mt; refinement = Refinement.Module_equation {path; definition}}
  and specif = function
    | Signature_item.Declaration s -> Signature_item.Declaration (spec s)
    | Signature_item.Module mt -> Signature_item.Module (mtype mt)
    | Signature_item.Module_type mt -> Signature_item.Module_type (mtype mt)
  in
  let rec elems sel =
    List.map
      (fun (l, se) ->
        match se with
        | Structure_item.Declaration d -> (l, Structure_item.Declaration (decl d))
        | Structure_item.Module m ->
          (l, Structure_item.Module {Module_binding.expr = module_expr m.Module_binding.expr; type_ = mtype m.type_})
        | Structure_item.Module_type mt -> (l, Structure_item.Module_type (mtype mt)) )
      sel
  and module_expr = function
    | Module_expr.Structure {path = mp; items = sel} -> Module_expr.Structure {path = mp; items = elems sel}
    | Module_expr.Functor {parameter = mbid; parameter_type = mt; body = me} ->
      Module_expr.Functor {parameter = mbid; parameter_type = mtype mt; body = module_expr me}
    | Module_expr.Path p -> Module_expr.Path p
    | Module_expr.Apply {functor_; argument} ->
      Module_expr.Apply {functor_ = module_expr functor_; argument = module_expr argument}
  in
  List.map (fun (mp, sel) -> (mp, elems sel)) s
