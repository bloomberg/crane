(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Putting back the temporaries {!Normalize} introduced.

    Normalize names every recursive call it takes out of an expression, so
    that loopification meets the call as a statement it can split the
    function at.  Where it does split, the name becomes frame state or the
    binding of [_result]; everywhere else it is a local the Rocq source never
    had.  This pass returns each such temporary to the one place it is read,
    which, where nothing was split, restores the expression Normalize took it
    out of: Normalize only binds a call from a strictly evaluated position,
    in evaluation order, and never out of a branch, a lambda or a let body.

    A temporary is known by its name ({!Mlutil.is_temporary_id}).  It goes
    back when it is read exactly once, by the first statement after the run
    of temporaries it heads, at a position that statement evaluates
    unconditionally -- never into a reference's initialiser or the scrutinee
    of a match that borrows it, where a reference into the inlined value
    would outlive it. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

(* Occurrences of [x] in a statement list, binding sites included: a
   temporary assigned to again is not one to inline. *)
let count_stmts x (stmts : stmt list) =
  let n = ref 0 in
  let rec visitor = {Cpp_ir.Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun _ -> ())}
  and expr (e : expr) =
    match e with
    | Local y when Id.equal x y -> incr n
    | _ -> Cpp_ir.Children.expr visitor e
  and stmt (s : stmt) =
    (match s with Bind_variable (y, _, _) when Id.equal x y -> incr n | _ -> ());
    Cpp_ir.Children.stmt visitor s
  in
  List.iter stmt stmts;
  !n

let count_stmt x s = count_stmts x [s]

(* Whether [e] evaluates each of its operands whenever it is evaluated: not a
   lambda, a conditional or a connective. *)
let evaluates_operands : expr -> bool = function
  | Lambda _ | Conditional _ | Binary ((And | Or), _, _) -> false
  | _ -> true

let rec is_reference_type : Cpp_ir.Lowered.Type.t -> bool = function
  | Reference _ -> true
  | Const t -> is_reference_type t
  | _ -> false

(* [e] with its read of [x] replaced by [v], if that read is evaluated
   whenever [e] is. *)
let rec subst_expr x (v : expr) (e : expr) : expr option =
  match e with
  | Local y when Id.equal x y -> Some v
  (* A move out of the temporary moves out of what it held: once, and only
     if that is an lvalue -- a move of a call's result would cost the copy
     elision it was written to give. *)
  | Move (Local y) when Id.equal x y -> Some (match v with Local _ | Access _ | Dereference _ -> Move v | _ -> v)
  | _ when not (evaluates_operands e) -> None
  | _ ->
    let found = ref false in
    let in_child c =
      if !found then c
      else
        match subst_expr x v c with
        | Some c' ->
          found := true;
          c'
        | None -> c
    in
    let e' = Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:in_child ~stmt:Fun.id ~type_:Fun.id ()) e in
    if !found then Some e' else None

(* [s] with its read of [x] replaced by [v], if [s] evaluates that read
   unconditionally and holds on to no reference into it: a value
   declaration, not a reference, and a match only if it takes its scrutinee
   by value or binds nothing of it, as a [bool]'s does. *)
let subst_stmt x v (s : stmt) : stmt option =
  let in_expr rebuild e = Option.map rebuild (subst_expr x v e) in
  match s with
  | Return (Some e) -> in_expr (fun e : stmt -> Return (Some e)) e
  | Expression e -> in_expr (fun e : stmt -> Expression e) e
  | Bind_variable (y, (Declare (ty, _) as t), e) when not (is_reference_type ty) ->
    in_expr (fun e : stmt -> Bind_variable (y, t, e)) e
  | Bind_variable (y, Existing, e) -> in_expr (fun e : stmt -> Bind_variable (y, Existing, e)) e
  | If i -> in_expr (fun c : stmt -> If {i with condition = c}) i.condition
  | Custom_match m
    when m.hold = Owned || List.for_all (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> b.params = []) m.branches ->
    in_expr (fun scrutinee : stmt -> Custom_match {m with scrutinee}) m.scrutinee
  | _ -> None

(* Whether [s] declares a temporary Normalize introduced. *)
let is_temporary : stmt -> bool = function
  | Bind_variable (y, Declare _, _) -> Mlutil.is_temporary_id y
  | _ -> false

(* Every local [e] names. *)
let names_expr (e : expr) =
  let acc = ref Id.Set.empty in
  let rec visitor = {Cpp_ir.Children.expr = (fun e -> expr e); stmt = (fun s -> Cpp_ir.Children.stmt visitor s); type_ = (fun _ -> ())}
  and expr (e : expr) =
    (match e with Local y -> acc := Id.Set.add y !acc | _ -> ());
    Cpp_ir.Children.expr visitor e
  in
  expr e;
  !acc

(* [s] with its moves of the locals [xs], a capture's included, made reads. *)
let rec read_not_moved xs (s : stmt) : stmt =
  let rec expr (e : expr) : expr =
    match e with
    | Move (Local y) when Id.Set.mem y xs -> Local y
    | Lambda l when List.exists (fun y -> Id.Set.mem y xs) l.moved ->
      expr (Lambda {l with moved = List.filter (fun y -> not (Id.Set.mem y xs)) l.moved})
    | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr ~stmt:(read_not_moved xs) ~type_:Fun.id ()) e
  in
  Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr ~stmt:(read_not_moved xs) ~type_:Fun.id ()) s

(* [rest] with [x] replaced by [v] in the first statement past the leading
   temporaries, if that is where [x] is read.  [v] is then evaluated after
   the temporaries it passes and with the rest of that statement, in an
   order C++ leaves open, where it was evaluated before them: what any of
   them moved that [v] reads is read there instead.  The ownership plan,
   reading the temporaries in sequence, may have taken a later one's read
   for a variable's last. *)
let inline_into x v rest =
  let read_by_v = read_not_moved (names_expr v) in
  let rec go = function
    | s :: rest when is_temporary s && count_stmt x s = 0 -> Option.map (fun rest -> read_by_v s :: rest) (go rest)
    | s :: rest -> Option.map (fun s -> s :: rest) (subst_stmt x v (read_by_v s))
    | [] -> None
  in
  go rest

(* The rewrite putting temporaries back in a statement list, an expression
   and a statement, the last first: by the time a temporary is considered,
   every temporary between it and its use has already gone back into that
   use.  [lambdas] says whether lambda bodies are included. *)
let restorer ~lambdas =
  let rec block : stmt list -> stmt list = function
    | [] -> []
    | s :: rest -> (
      let rest = block rest in
      let s : stmt = stmt s in
      match s with
      | Bind_variable (x, Declare _, v) when Mlutil.is_temporary_id x && count_stmts x rest = 1 ->
        Option.default (s :: rest) (inline_into x v rest)
      | _ -> s :: rest )
  and stmt s = Cpp_ir.Map.stmt (children ()) s
  and expr (e : expr) =
    match e with
    | Lambda _ when not lambdas -> e
    | _ -> Cpp_ir.Map.expr (children ()) e
  and children () = Cpp_ir.Map.make ~stmts:block ~expr ~stmt ~type_:Fun.id () in
  children ()

(** [own_stmts body] is [body] with the temporaries of its own statements put
    back, those of any lambda in it left: the view a transform of [body]
    alone reads, each lambda being transformed on its own.  Asked by Loopify,
    which reads a function body before it is finished. *)
let own_stmts body = (restorer ~lambdas:false).stmts body

(** [decl d] is [d] with its temporaries put back. *)
let decl (d : Cpp_ir.Lowered.Decl.t) = Cpp_ir.Map.decl (restorer ~lambdas:true) d
