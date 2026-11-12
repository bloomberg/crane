(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small local simplifications.  See [cpp_simplify.mli]. *)

open Names
module V = Cpp_ir.Variables

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

(* A [bool]: what a comparison or a connective yields. *)
let is_bool : expr -> bool = function
  | Binary ((Equal | Not_equal | And | Or), _, _) | Unary (Not, _) | Literal (Bool _) -> true
  | _ -> false

(* A function type, as written or through an alias for one ([stateT]). *)
let rec is_function_type : ty -> bool = function
  | Function _ -> true
  | Entity_application (GlobRef.ConstRef kn, _, _) -> (
    match Table.lookup_typedef_unchecked kn with
    | Some ml -> ( match Mlutil.ml_resolve ml with Miniml.Tarr _ -> true | _ -> false )
    | None -> false )
  | In_namespace (_, t) -> is_function_type t
  | _ -> false

(* Drop each binding of a pure value nothing after it reads or assigns. *)
let rec drop_unused : stmt list -> stmt list = function
  | [] -> []
  | Bind_variable (x, Declare _, e) :: rest
    when V.pure e && (not (V.mem x (V.free_in_body rest))) && not (Id.Set.mem x (V.assigned rest)) ->
    drop_unused rest
  | s :: rest -> s :: drop_unused rest

(* The variable [e] reads a member of, through a chain of member reads: a
   field, a pair's component through its projection mapping, a
   [crane::field]'s contents. *)
let rec member_root : expr -> Id.t option = function
  | Access (Dot, e, _) | Member (e, _) | Project (e, _, _) -> path_root e
  | Call (_, Entity (_, _, Some {inline = Some {shape = Pair_projection _; _}; _}), [e])
  | Call (_, Runtime Crane_rt.Unbox_field, [e]) ->
    path_root e
  | _ -> None

and path_root : expr -> Id.t option = function Local x -> Some x | e -> member_root e

(* Whether some expression of [stmts], a lambda's body included, holds of
   [p]. *)
let exists_expr p (stmts : stmt list) =
  let exception Found in
  let rec visitor = {Cpp_ir.Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun _ -> ())}
  and expr e =
    if p e then raise_notrace Found;
    Cpp_ir.Children.expr visitor e
  and stmt s = Cpp_ir.Children.stmt visitor s in
  match List.iter stmt stmts with () -> false | exception Found -> true

(* Whether [stmts] move from [v] anywhere, or from anything inside it, or
   reach into it mutably -- a reuse arm decomposes its scrutinee through
   [v_mut()]. *)
let takes_from v stmts =
  exists_expr
    (function
      | Move e -> path_root e = Some v
      | Access (_, e, f) | Access_call (_, e, f, _) -> String.equal (Id.to_string f) "v_mut" && path_root e = Some v
      | _ -> false )
    stmts

(* Whether a value of [ty] costs more to copy than to move. *)
let worth_moving ty = Ownership_ir.worth_moving_cpp (Cpp_ir_to_legacy_minicpp.ty ty)

(* A local copied out of a member of another -- [T2 s0 = si.first] -- is a
   [const] reference to it instead, where the other is neither assigned nor
   moved from afterwards, and the local neither assigned nor taken from: the
   other outlives it, and no pass after this one moves from it, so what it
   names stays put.  The copy it saved is made only by a use that keeps the
   value.  A type a copy costs nothing for -- a scalar, a pointer -- is
   copied as it was. *)
let rec bind_by_reference : stmt list -> stmt list = function
  | [] -> []
  | Bind_variable (x, Declare (ty, binder), rhs) :: rest
    when (match ty with Reference _ | Const (Reference _) -> false | _ -> true)
         && (ty = Auto || worth_moving ty)
         && ( match member_root rhs with
            | Some v ->
              let assigned = V.assigned rest in
              not (Id.Set.mem x assigned || Id.Set.mem v assigned || takes_from v rest || takes_from x rest)
            | None -> false ) ->
    let ty : ty = match ty with Const _ -> ty | _ -> Const ty in
    Bind_variable (x, Declare (Reference (Lvalue, ty), binder), rhs) :: bind_by_reference rest
  | s :: rest -> s :: bind_by_reference rest

(* [stmts] with every match on one of [ids] borrowing, and the moves out of
   the fields such a match binds dropped: what a borrowing match binds is a
   [const] view, so the matches on it borrow too. *)
let borrow_matches_on ids (stmts : stmt list) =
  let rec mentions ids (e : expr) =
    (match e with Local x -> V.mem x ids | _ -> false)
    ||
    let found = ref false in
    let ignore_ _ = () in
    Cpp_ir.Children.expr {expr = (fun c -> found := !found || mentions ids c); stmt = ignore_; type_ = ignore_} e;
    !found
  in
  let strip_moves bound =
    let rec expr : expr -> expr = function
      | Move (Local x) when V.mem x bound -> Local x
      | e -> Cpp_ir.Map.expr (children ()) e
    and stmt s = Cpp_ir.Map.stmt (children ()) s
    and children () = Cpp_ir.Map.make ~expr ~stmt ~type_:Fun.id () in
    List.map stmt
  in
  let rec stmt ids : stmt -> stmt = function
    | Match (scrut, branches, default) ->
      let through = mentions ids scrut.expr in
      Match
        ( {scrut with owned = scrut.owned && not through},
          List.map
            (fun (b : _ Cpp_ir.Stmt.Match.branch) ->
              if not through then {b with body = List.map (stmt ids) b.body}
              else
                let bound = List.map (fun (f : _ Cpp_ir.Stmt.Match.field_binding) -> f.name) b.field_bindings in
                let views = (match b.var with Some v -> v :: bound | None -> bound) @ ids in
                {b with body = strip_moves bound (List.map (stmt views) b.body)} )
            branches,
          Option.map (List.map (stmt ids)) default )
    | s -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:(stmt ids) ~type_:Fun.id ()) s
  in
  List.map (stmt ids) stmts

(* [stmts] with every match on a local bound by [const] reference or by
   pointer borrowing: such a local names a value something else owns. *)
let borrow_bound_matches (stmts : stmt list) =
  let ids = ref [] in
  let rec scan (s : stmt) =
    ( match s with
    | Bind_variable (x, Declare ((Reference (Lvalue, Const _) | Pointer _), _), _) -> ids := x :: !ids
    | _ -> () );
    let nested s =
      scan s;
      s
    in
    ignore (Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:nested ~type_:Fun.id ()) s)
  in
  List.iter scan stmts;
  if !ids = [] then stmts else borrow_matches_on !ids stmts

(* Under Reuse, a match-only scrutinee may be marked owned so that a reuse arm
   can consume it; one reached through a [const] reference or a pointer cannot
   be, and its matches borrow. *)
let borrow_bound ss = if Table.reuse () then borrow_bound_matches ss else ss

let rec stmts ss = borrow_bound (bind_by_reference (drop_unused (List.map stmt ss)))

and stmt (s : stmt) : stmt =
  match s with
  | If i -> (
    match expr i.condition with
    | Literal (Bool b) -> Block (stmts (if b then i.then_ else i.else_))
    | c -> (
      match (stmts i.then_, stmts i.else_) with
      | [Return (Some (Literal (Bool true)))], [Return (Some (Literal (Bool false)))] when is_bool c -> Return (Some c)
      | then_, else_ -> If {condition = c; then_; else_} ) )
  | _ -> Cpp_ir.Map.stmt (children ()) s

and expr (e : expr) : expr =
  match e with
  | Conditional (Literal (Bool b), x, y) -> expr (if b then x else y)
  (* [k(a)(b)] through a local: a curried closure applied to both arguments
     at once, which allocates nothing for the closure in between when [k]
     was written as one lambda returning another. *)
  | Call (sg, Call (_, ((Local _ | Move (Local _)) as k), [a]), [b]) ->
    let b = expr b in
    let a = expr a in
    Call (sg, Runtime Crane_rt.Apply2, [k; a; b])
  (* A lambda that only returns another lambda hands it back unboxed: the
     [fn] it converts into still boxes it where it is kept, and
     [crane::apply2] runs it where it is applied at once. *)
  | Lambda ({return_type = Some t; body = [Return (Some (Lambda _))]; _} as l) when is_function_type t ->
    Cpp_ir.Map.expr (children ()) (Lambda {l with return_type = None})
  | _ -> Cpp_ir.Map.expr (children ()) e

and children () = Cpp_ir.Map.make ~stmts ~expr ~stmt ~type_:Fun.id ()

let transform_decl d = Cpp_ir.Map.decl (children ()) d
