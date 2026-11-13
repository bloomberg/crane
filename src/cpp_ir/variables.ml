(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The local variables code refers to, binds and assigns. *)

open Names
open Grammar

let mem x xs = List.exists (Id.equal x) xs
let without bound xs = List.filter (fun x -> not (mem x bound)) xs

(** The variables an expression refers to without binding them, in the
    order they are met, repeated as often as they are met.  A call's
    arguments are met first to last; a [decltype] in a type is not read. *)
let rec free_in_expr : type p. p Expr.t -> Id.t list =
 fun e ->
  let expr = free_in_expr and many es = List.concat_map free_in_expr es in
  match e with
  | Local x -> [x]
  | Call (_, f, args) -> expr f @ many args
  | Access_call (_, e, _, args) -> expr e @ many args
  | Method_call m -> expr m.receiver @ many m.args
  | Projection p -> expr p.record @ many p.args
  | Move e | Dereference e | Forward (_, e) | Member (e, _) | Project (e, _, _) | Access (_, e, _) | Scope (e, _, _)
    ->
    expr e
  | Binary (_, a, b) -> expr a @ expr b
  | Aggregate a -> many a.values
  | Local_aggregate a -> many a.values
  | Lambda l -> without (List.filter_map snd l.params) (free_in_body l.body)
  | Requires q -> many (List.map fst q.constraints)
  | _ ->
    let found = ref [] in
    let ignore_ _ = () in
    Children.expr {expr = (fun c -> found := !found @ expr c); stmt = ignore_; type_ = ignore_} e;
    !found

(** The variables a statement refers to without binding them: what a
    branch, a loop or a declaring [if] binds is not free in it. *)
and free_in_stmt : type p. p Stmt.t -> Id.t list =
 fun s ->
  let expr = free_in_expr and body = free_in_body in
  match s with
  | Return (Some e) | Expression e | Bind_variable (_, _, e) | Structured_binding (_, e) -> expr e
  | Assign (l, e) -> expr l @ expr e
  | If i -> expr i.condition @ body i.then_ @ body i.else_
  | If_constexpr i -> body i.then_ @ body i.else_
  | Custom_match m ->
    expr m.scrutinee
    @ List.concat_map
        (fun (b : p Custom_match.branch) ->
          without (List.map (fun (p : p Custom_match.param) -> p.name) b.params) (body b.body) )
        m.branches
  | Switch w ->
    expr w.scrutinee @ List.concat_map (fun (_, b) -> body b) w.branches
    @ (match w.default with Some ss -> body ss | None -> [])
  | Match (scrutinee, branches, default) ->
    expr scrutinee.expr
    @ List.concat_map
        (fun (b : p Match.branch) ->
          let bound =
            List.map (fun (f : p Match.field_binding) -> f.name) b.field_bindings
            @ match b.var with Some x -> [x] | None -> []
          in
          without bound (List.concat_map expr b.extra_conditions @ body b.body) )
        branches
    @ (match default with Some ss -> body ss | None -> [])
  | Block ss -> body ss
  | If_declaration i -> expr i.init @ without [i.name] (body i.then_) @ body i.else_
  | For_range (x, e, b) -> expr e @ without [x] (body b)
  | While (c, b) -> expr c @ body b
  | Foreign_block b -> List.concat_map expr b.values
  | Return None | Declare _ | Throw _ | Assert _ | Foreign_text _ | Comment _ | Local_struct _ | Local_type_alias _
  | Declare_value_initialized _ | Continue | Break ->
    []

(** The variables a statement list refers to without binding them, a
    variable a statement declares not free in the statements after it. *)
and free_in_body : type p. p Stmt.t list -> Id.t list =
 fun stmts ->
  let rec go defined = function
    | [] -> []
    | (s : p Stmt.t) :: rest ->
      let declared =
        match s with
        | Bind_variable (x, Declare _, _) | Declare (x, _, _) | Declare_value_initialized (x, _) -> [x]
        | Foreign_block b -> [b.result]
        | Structured_binding (xs, _) -> xs
        | _ -> []
      in
      without defined (free_in_stmt s) @ go (declared @ defined) rest
  in
  go [] stmts

(** The variables [stmts] assign after declaring them, anywhere, a lambda's
    body included. *)
let assigned : type p. p Stmt.t list -> Id.Set.t =
 fun stmts ->
  let acc = ref Id.Set.empty in
  let rec visitor = {Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun _ -> ())}
  and stmt (s : p Stmt.t) =
    ( match s with
    | Bind_variable (x, Existing, _) | Assign (Local x, _) | Expression (Binary (Assign, Local x, _)) ->
      acc := Id.Set.add x !acc
    | _ -> () );
    Children.stmt visitor s
  and expr (e : p Expr.t) =
    (match e with Binary (Assign, Local x, _) -> acc := Id.Set.add x !acc | _ -> ());
    Children.expr visitor e
  in
  List.iter stmt stmts;
  !acc

(** The variables [stmts] declare at any depth, each once, in the order they
    are first declared: the names a body would carry into any scope it is
    spliced into. *)
let declared : type p. p Stmt.t list -> Id.t list =
 fun stmts ->
  let acc = ref [] in
  let note x = if not (mem x !acc) then acc := x :: !acc in
  let rec visitor = {Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun _ -> ())}
  and stmt (s : p Stmt.t) =
    ( match s with
    | Bind_variable (x, Declare _, _)
    | Declare (x, _, _)
    | Declare_value_initialized (x, _)
    | If_declaration {name = x; _}
    | For_range (x, _, _) ->
      note x
    | Structured_binding (xs, _) -> List.iter note xs
    | Foreign_block b -> note b.result
    | Match (_, branches, _) ->
      List.iter
        (fun (b : p Match.branch) ->
          Option.iter note b.var;
          List.iter (fun (f : p Match.field_binding) -> note f.name) b.field_bindings )
        branches
    | Custom_match m ->
      List.iter
        (fun (b : p Custom_match.branch) -> List.iter (fun (p : p Custom_match.param) -> note p.name) b.params)
        m.branches
    | _ -> () );
    Children.stmt visitor s
  and expr (e : p Expr.t) =
    (match e with Lambda l -> List.iter (fun (_, x) -> Option.iter note x) l.params | _ -> ());
    Children.expr visitor e
  in
  List.iter stmt stmts;
  List.rev !acc

(** Whether evaluating [e] has no effect: a variable, a literal, a
    constructor applied to pure arguments, an aggregate of them, an operator
    other than assignment or address-of on them. *)
let rec pure : type p. p Expr.t -> bool = function
  | Local _ | Literal _ | Enum_value _ | Numeral _ | Entity (GlobRef.ConstructRef _, _, _) -> true
  | Aggregate a -> List.for_all pure a.values
  | Local_aggregate a -> List.for_all pure a.values
  | Braced es -> List.for_all pure es
  | Call (_, Entity (GlobRef.ConstructRef _, _, _), args) -> List.for_all pure args
  | Binary (o, a, b) -> o <> Assign && pure a && pure b
  | Unary (o, a) -> o <> Address_of && pure a
  | _ -> false

(** Whether [e] evaluates each of its operands whenever it is evaluated: not
    a lambda, a conditional or a connective. *)
let evaluates_operands : type p. p Expr.t -> bool = function
  | Lambda _ | Conditional _ | Binary ((And | Or), _, _) -> false
  | _ -> true

(** [lambda_needs_capture params body] is [(needs_capture, uses_this)]:
    whether a lambda of these parameters and this body names a variable it
    neither binds nor declares -- its own, or one a nested lambda names --
    and so must capture, and whether it names the enclosing [this]. *)
let lambda_needs_capture : type p. (p Type.t * Id.t option) list -> p Stmt.t list -> bool * bool =
 fun params body ->
  let names ps = List.fold_left (fun acc (_, x) -> match x with Some id -> Id.Set.add id acc | None -> acc) Id.Set.empty ps in
  let uses_this = ref false in
  let rec collect_from_expr (refs, decls) (e : p Expr.t) =
    match e with
    | Local id -> (Id.Set.add id refs, decls)
    | Dereference e -> collect_from_expr (refs, decls) e
    | This | Shared_from_this _ ->
      uses_this := true;
      (refs, decls)
    | Lambda {params = inner_params; body = inner_body; _} ->
      let inner_refs, inner_decls = List.fold_left collect_from_stmt (Id.Set.empty, Id.Set.empty) inner_body in
      let inner_free = Id.Set.diff inner_refs (Id.Set.union (names inner_params) inner_decls) in
      (Id.Set.union refs inner_free, decls)
    | _ ->
      let acc = ref (refs, decls) in
      Subterms.expr
        ~expr:(fun e' -> acc := collect_from_expr !acc e')
        ~stmts:(fun stmts -> acc := List.fold_left collect_from_stmt !acc stmts)
        e;
      !acc
  and collect_from_stmt (refs, decls) (s : p Stmt.t) =
    match s with
    | Declare (id, _, _) -> (refs, Id.Set.add id decls)
    | Bind_variable (id, binding, e) -> (
      let refs', decls' = collect_from_expr (refs, decls) e in
      match binding with
      | Declare _ | Declare_static _ -> (refs', Id.Set.add id decls')
      | Existing -> (Id.Set.add id refs', decls') )
    | Assign (lhs, e) ->
      let refs', decls' = collect_from_expr (refs, decls) lhs in
      collect_from_expr (refs', decls') e
    | Custom_match m ->
      List.fold_left
        (fun (r, d) (b : p Custom_match.branch) ->
          let branch_decls = List.fold_left (fun acc (q : p Custom_match.param) -> Id.Set.add q.name acc) d b.params in
          List.fold_left collect_from_stmt (r, branch_decls) b.body )
        (collect_from_expr (refs, decls) m.scrutinee)
        m.branches
    | Foreign_block b ->
      let refs', decls' = List.fold_left collect_from_expr (refs, decls) b.values in
      (refs', Id.Set.add b.result decls')
    | Match (scrut, branches, default) -> (
      let refs, decls = collect_from_expr (refs, decls) scrut.expr in
      let acc =
        List.fold_left
          (fun acc (br : p Match.branch) ->
            let refs', decls' = List.fold_left collect_from_expr acc br.extra_conditions in
            let branch_decls =
              let d = List.fold_left (fun d (fb : p Match.field_binding) -> Id.Set.add fb.name d) decls' br.field_bindings in
              match br.var with Some id -> Id.Set.add id d | None -> d
            in
            List.fold_left collect_from_stmt (refs', branch_decls) br.body )
          (refs, decls) branches
      in
      match default with Some stmts -> List.fold_left collect_from_stmt acc stmts | None -> acc )
    | _ ->
      let acc = ref (refs, decls) in
      Subterms.stmt
        ~expr:(fun e -> acc := collect_from_expr !acc e)
        ~stmts:(fun stmts -> acc := List.fold_left collect_from_stmt !acc stmts)
        s;
      !acc
  in
  let all_refs, local_decls = List.fold_left collect_from_stmt (Id.Set.empty, Id.Set.empty) body in
  let free_vars = Id.Set.diff all_refs (Id.Set.union (names params) local_decls) in
  ((not (Id.Set.is_empty free_vars)) || !uses_this, !uses_this)

(** Whether [e] is a lambda that captures nothing, or one such invoked at
    once with no argument: a value that names no variable of its scope, so
    the same wherever it is evaluated. *)
let closed_lambda : type p. p Expr.t -> bool =
 fun e ->
  let captureless (e : p Expr.t) =
    match e with Lambda {params; body; _} -> not (fst (lambda_needs_capture params body)) | _ -> false
  in
  match e with
  | Lambda _ -> captureless e
  | Call (_, f, []) -> captureless f
  | _ -> false
