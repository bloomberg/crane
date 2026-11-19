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
    match Base.Table.lookup_typedef_unchecked kn with
    | Some ml -> ( match Base.Core_util.core_resolve ml with Core.Type.Arrow _ -> true | _ -> false )
    | None -> false )
  | In_namespace (_, t) -> is_function_type t
  | _ -> false

(* Whether a match on [e] evaluates nothing with an effect: a pure value,
   or the variant a pure value holds, read through its [v()] accessor. *)
let rec pure_scrutinee : expr -> bool = function
  | Call (_, Access (_, e, v), []) when Id.equal v (Id.of_string "v") -> pure_scrutinee e
  | Dereference e -> pure_scrutinee e
  | e -> V.pure e

(* Whether [e] is a lambda invoked in place only to choose, on pure tests,
   among pure values, which {!Erasure.lower_conditionals} makes the choice:
   evaluating it has no effect. *)
let rec pure_choice : expr -> bool = function
  | Call (_, Lambda {params = []; body; _}, []) ->
    let rec pure_stmt : stmt -> bool = function
      | Return (Some e) | Bind_variable (_, Declare _, e) -> V.pure e || pure_choice e
      | Match (scrut, branches, default) ->
        pure_scrutinee scrut.expr
        && List.for_all
             (fun (b : _ Cpp_ir.Stmt.Match.branch) ->
               List.for_all V.pure b.extra_conditions && List.for_all pure_stmt b.body )
             branches
        && (match default with Some d -> List.for_all pure_stmt d | None -> true)
      | If i -> V.pure i.condition && List.for_all pure_stmt i.then_ && List.for_all pure_stmt i.else_
      | Block ss -> List.for_all pure_stmt ss
      | _ -> false
    in
    List.for_all pure_stmt body
  | _ -> false

(* [stmts] without the assignments to [x], where nothing reads it: one of a
   pure value is dropped, one of a call becomes the call, run for whatever
   it does; and without the statements left doing nothing but choosing, on
   pure tests, between branches that did only that -- a match the value of a
   [let] was lowered to, each of its branches assigning the local the [let]
   declared, after what a branch bound for it alone is dropped too. *)
let rec unassign x (stmts : stmt list) : stmt list =
  let quiet = List.for_all (fun (ss : stmt list) -> ss = []) in
  let body ss = drop_unused (unassign x ss) in
  List.concat_map
    (fun (s : stmt) : stmt list ->
      match s with
      | Bind_variable (y, Existing, e) when Id.equal x y && (V.pure e || pure_choice e) -> []
      | Bind_variable (y, Existing, (Call _ as e)) when Id.equal x y -> [Expression e]
      | Match (scrut, branches, default) ->
        let branches = List.map (fun (b : _ Cpp_ir.Stmt.Match.branch) -> {b with body = body b.body}) branches in
        let default = Option.map body default in
        if pure_scrutinee scrut.expr
           && List.for_all (fun (b : _ Cpp_ir.Stmt.Match.branch) -> List.for_all V.pure b.extra_conditions) branches
           && quiet
                (List.map (fun (b : _ Cpp_ir.Stmt.Match.branch) -> b.body) branches
                @ match default with Some d -> [d] | None -> [] )
        then []
        else [Match (scrut, branches, default)]
      | If i ->
        let then_ = body i.then_ and else_ = body i.else_ in
        if V.pure i.condition && quiet [then_; else_] then [] else [If {i with then_; else_}]
      | Custom_match m ->
        (* A mapped match only takes its scrutinee apart: with nothing left
           in its branches, it does nothing a pure scrutinee could. *)
        let branches = List.map (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> {b with body = body b.body}) m.branches in
        if V.pure m.scrutinee && quiet (List.map (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> b.body) branches)
        then []
        else [Custom_match {m with branches}]
      | Block ss -> ( match body ss with [] -> [] | ss -> [Block ss] )
      | s -> [s] )
    stmts

(* Drop each binding of a pure value nothing after it reads or assigns, and
   each local declared without one that nothing after it reads, with what is
   assigned to it ({!unassign}). *)
and drop_unused : stmt list -> stmt list = function
  | [] -> []
  | Bind_variable (x, Declare _, e) :: rest
    when V.pure e && (not (V.mem x (V.free_in_body rest))) && not (Id.Set.mem x (V.assigned rest)) ->
    drop_unused rest
  | (Declare (x, _, _) as s) :: rest -> (
    let rest' = unassign x rest in
    match V.mem x (V.free_in_body rest') || Id.Set.mem x (V.assigned rest') with
    | false -> drop_unused rest'
    | true -> s :: drop_unused rest )
  | s :: rest -> s :: drop_unused rest

(* The variable [e] reads a member of, through a chain of member reads: a
   field, a pair's component through its projection mapping, a
   [crane::field]'s contents. *)
let rec member_root : expr -> Id.t option = function
  | Access (Dot, e, _) | Member (e, _) | Project (e, _, _) -> path_root e
  | Call (_, Entity (_, _, Some {inline = Some {shape = Pair_projection _; _}; _}), [e])
  | Call (_, Runtime Cpp_ir.Crane_rt.Unbox_field, [e]) ->
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
let worth_moving = Ownership_ir.Region.worth_moving_cpp

(* [stmts] without the moves out of the locals [bound]: fields a borrowing
   match binds, [const] views a move would only copy. *)
let strip_moves bound =
  let rec expr : expr -> expr = function
    | Move (Local x) when V.mem x bound -> Local x
    | e -> Cpp_ir.Map.expr (children ()) e
  and stmt s = Cpp_ir.Map.stmt (children ()) s
  and children () = Cpp_ir.Map.make ~expr ~stmt ~type_:Fun.id () in
  List.map stmt

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
    | s -> Cpp_ir.Map.stmt (within ids) s
  (* A lambda in a branch -- an immediately invoked one computing a value
     -- sees the same views: its matches on them borrow too. *)
  and within ids = Cpp_ir.Map.make ~expr:(expr ids) ~stmt:(stmt ids) ~type_:Fun.id ()
  and expr ids e = Cpp_ir.Map.expr (within ids) e in
  List.map (stmt ids) stmts

(* A local copied out of a member of another -- [T2 s0 = si.first] -- is a
   [const] reference to it instead, where the other is neither assigned nor
   moved from afterwards, and the local neither assigned nor taken from: the
   other outlives it, and no pass after this one moves from it, so what it
   names stays put.  The copy it saved is made only by a use that keeps the
   value.  A type a copy costs nothing for -- a scalar, a pointer -- is
   copied as it was.  A match on the local, which could take the copy apart,
   borrows the view instead ({!borrow_matches_on}). *)
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
    Bind_variable (x, Declare (Reference (Lvalue, ty), binder), rhs)
    :: bind_by_reference rest
  | s :: rest -> s :: bind_by_reference rest

(* Whether a local declared at [ty] is [const] in C++: declared [const],
   a [const] reference, or a pointer to [const]. *)
let const_declared : ty -> bool = function
  | Const _ | Reference (_, Const _) | Pointer (Const _) -> true
  | _ -> false

(* Whether a match over [branches] may take its scrutinee apart, a value it
   owns, given the locals [consts] that are [const] where it is written:
   not when its scrutinee reads one of them -- a [const] value cannot be
   taken apart. *)
let may_take_apart consts (scrut : _ Cpp_ir.Grammar.Match.scrutinee) _branches =
  scrut.owned && not (List.exists (fun x -> Id.Set.mem x consts) (V.free_in_expr scrut.expr))

(* The access mode of every match, settled over the finished declaration: a
   match the plan made over Core marked owned borrows where it may not take
   its scrutinee apart ({!may_take_apart}), and the moves out of the fields
   it binds are dropped.  A local is [const] where a match is written when
   its declaration says so, when a by-copy lambda between its declaration
   and the match captured it -- a closure is never [mutable], so its
   captures are [const] in its body -- or when a borrowing match bound it.
   The rewrite of a declaration's children, none [const] at its top. *)
let borrow_const_matches =
  let declare consts x ty = if const_declared ty then Id.Set.add x consts else Id.Set.remove x consts in
  let rec block consts : stmt list -> stmt list = function
    | [] -> []
    | s :: rest ->
      let s = stmt consts s in
      let consts =
        match s with
        | Declare (x, ty, _) | Declare_value_initialized (x, ty) | Bind_variable (x, Declare (ty, _), _) ->
          declare consts x ty
        | _ -> consts
      in
      s :: block consts rest
  and stmt consts (s : stmt) : stmt =
    match s with
    | Match (scrut, branches, default) ->
      let scrut = {scrut with expr = expr consts scrut.expr} in
      let owned = may_take_apart consts scrut branches in
      let borrowed = scrut.owned && not owned in
      let branch (b : _ Cpp_ir.Stmt.Match.branch) =
        let bound = List.map (fun (f : _ Cpp_ir.Stmt.Match.field_binding) -> f.name) b.field_bindings in
        let bound = match b.var with Some v -> v :: bound | None -> bound in
        let consts =
          List.fold_left (fun c x -> if owned then Id.Set.remove x c else Id.Set.add x c) consts bound
        in
        let body = block consts b.body in
        { b with
          extra_conditions = List.map (expr consts) b.extra_conditions;
          body = (if borrowed then strip_moves bound body else body) }
      in
      Match ({scrut with owned}, List.map branch branches, Option.map (block consts) default)
    | _ -> Cpp_ir.Map.stmt (within consts) s
  and expr consts (e : expr) : expr =
    match e with
    | Lambda l ->
      let consts =
        match l.capture with
        | Stored | Written (By_copy _) -> Id.Set.union consts (Id.Set.of_list (V.free_in_expr e))
        | Runs_in_place | Written (By_reference | Nothing) -> consts
      in
      let consts =
        List.fold_left (fun c (ty, x) -> match x with Some x -> declare c x ty | None -> c) consts l.params
      in
      Lambda (Cpp_ir.Map.lambda (within consts) l)
    | _ -> Cpp_ir.Map.expr (within consts) e
  and within consts = Cpp_ir.Map.make ~stmts:(block consts) ~expr:(expr consts) ~stmt:(stmt consts) ~type_:Fun.id () in
  within Id.Set.empty

let rec stmts ss = bind_by_reference (drop_unused (List.map stmt ss))

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
    Call (sg, Runtime Cpp_ir.Crane_rt.Apply2, [k; a; b])
  (* A lambda that only returns another lambda hands it back unboxed: the
     [fn] it converts into still boxes it where it is kept, and
     [crane::apply2] runs it where it is applied at once. *)
  | Lambda ({return_type = Some t; body = [Return (Some (Lambda _))]; _} as l) when is_function_type t ->
    Cpp_ir.Map.expr (children ()) (Lambda {l with return_type = None})
  | _ -> Cpp_ir.Map.expr (children ()) e

and children () = Cpp_ir.Map.make ~stmts ~expr ~stmt ~type_:Fun.id ()

(* The const-scrutinee rule runs once over the finished declaration, after
   the rewrites above have settled which locals are [const]. *)
let transform_decl d = Cpp_ir.Map.decl borrow_const_matches (Cpp_ir.Map.decl (children ()) d)
