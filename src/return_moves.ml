(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The moves a [return] writes.  See [return_moves.mli]. *)

open Names
module IdMap = Id.Map

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

(* Whether a local declared at [ty] refers to a value held elsewhere. *)
let rec is_borrowed : Cpp_ir.Lowered.Type.t -> bool = function
  | Reference _ | Const _ -> true
  | In_namespace (_, t) -> is_borrowed t
  | _ -> false

(* What a [return] moves without being told.  A call or a construction is
   built in the caller's object, so a move around it only suppresses copy
   elision.  So is a variable C++ moves implicitly -- a local or parameter of
   the innermost function, held by value.  A structured binding, a reference,
   a loop variable and, inside a lambda, whatever it captures are not: a
   return of one copies unless the move is written. *)
type held = Moved_on_return | Copied_on_return

(* Whether [e] is a call or a construction, built in the caller's object. *)
let prvalue : expr -> bool = function
  | Call _ | Access_call _ | Method_call _ | Projection _ | Aggregate _ | Local_aggregate _ -> true
  | _ -> false

let drop_return_moves d =
  let hold env ids h = List.fold_left (fun env id -> IdMap.add id h env) env ids in
  (* A name not declared where this walk sees it, such as one a foreign
     fragment declares, is taken to be moved on return: its move is dropped. *)
  let held env x = try IdMap.find x env with Not_found -> Moved_on_return in
  let by_type ty = if is_borrowed ty then Copied_on_return else Moved_on_return in
  let rec stmts env = function
    | [] -> []
    | s :: rest -> stmt env s :: stmts (declare env s) rest
  and declare env : stmt -> _ = function
    | Bind_variable (id, Declare (ty, _), _) -> hold env [id] (by_type ty)
    | Declare (id, _, _) | Declare_value_initialized (id, _) -> hold env [id] Moved_on_return
    | Structured_binding (ids, _) -> hold env ids Copied_on_return
    | _ -> env
  and stmt env (s : stmt) : stmt =
    match s with
    | Return (Some (Move (Local x as v))) when held env x = Moved_on_return -> Return (Some v)
    | Return (Some (Move e)) when prvalue e -> Return (Some (expr env e))
    | Match (scrut, branches, els) ->
      let branch (b : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Match.branch) : _ Cpp_ir.Stmt.Match.branch =
        let fields = List.map (fun (fb : _ Cpp_ir.Stmt.Match.field_binding) -> fb.name) b.field_bindings in
        let bound = match b.var with Some v -> v :: fields | None -> fields in
        let env = hold env bound Copied_on_return in
        {b with extra_conditions = List.map (expr env) b.extra_conditions; body = stmts env b.body}
      in
      Match ({scrut with expr = expr env scrut.expr}, List.map branch branches, Option.map (stmts env) els)
    | Custom_match m ->
      let branch (b : _ Cpp_ir.Stmt.Custom_match.branch) : _ Cpp_ir.Stmt.Custom_match.branch =
        let names = List.map (fun (p : _ Cpp_ir.Stmt.Custom_match.param) -> p.name) b.params in
        {b with body = stmts (hold env names Copied_on_return) b.body}
      in
      Custom_match {m with scrutinee = expr env m.scrutinee; branches = List.map branch m.branches}
    | If_declaration i ->
      let inner = hold env [i.name] (by_type i.type_) in
      If_declaration {i with init = expr env i.init; then_ = stmts inner i.then_; else_ = stmts inner i.else_}
    | For_range (id, e, body) -> For_range (id, expr env e, stmts (hold env [id] Copied_on_return) body)
    | _ -> Cpp_ir.Map.stmt (children env) s
  and expr env (e : expr) : expr =
    match e with
    | Lambda l ->
      let captured = IdMap.map (fun _ -> Copied_on_return) env in
      let own = List.filter_map snd l.params in
      Lambda {l with body = stmts (hold captured own Moved_on_return) l.body}
    | _ -> Cpp_ir.Map.expr (children env) e
  and children env = Cpp_ir.Map.make ~stmts:(stmts env) ~expr:(expr env) ~stmt:(stmt env) ~type_:Fun.id () in
  Cpp_ir.Map.decl (children IdMap.empty) d
