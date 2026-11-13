(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Settling the constraints of callable template parameters, from the
    bodies that call them.  See [cpp_constraints.mli]. *)

open Names
open Cpp_ir.Grammar

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type decl = Cpp_ir.Lowered.Decl.t
type parameters = Cpp_ir.Lowered.phase Template.parameters

let iter_expr ~expr ~stmts e = Cpp_ir.Subterms.expr ~expr ~stmts e
let iter_stmt ~expr ~stmts s = Cpp_ir.Subterms.stmt ~expr ~stmts s

let tvar_is = Cpp_ir.Type.is_variable_named

(** The value parameters [body] only ever hands to a representation-tolerant
    helper: erased into storage ([crane_erase_fn]) or applied through
    [crane_call_erased].  Those adapt whatever they are given, so the
    signature has nothing to say about how such a callback is called. *)
let erased_into_storage_ids (body : stmt list) =
  let ids = ref Id.Set.empty and applied = ref Id.Set.empty in
  let rec name : expr -> Id.t option = function
    | Local id -> Some id
    | Move e | Forward (_, e) -> name e
    | _ -> None
  in
  let add set e = Option.iter (fun id -> set := Id.Set.add id !set) (name e) in
  let rec check_expr (e : expr) =
    ( match e with
    | Erase_callable (_, inner) -> add ids inner
    | Tolerant_call (callee, _) -> add ids callee
    (* Applied here, so the signature does have something to claim -- even if
       the same callback is also handed to a helper elsewhere in the body. *)
    | Call (_, callee, _) -> add applied callee
    | _ -> () );
    iter_expr ~expr:check_expr ~stmts:(List.iter check_stmt) e
  and check_stmt s = iter_stmt ~expr:check_expr ~stmts:(List.iter check_stmt) s in
  List.iter check_stmt body;
  Id.Set.diff !ids !applied

(** Whether the template parameter [id] types a value parameter that [body]
    only erases into storage ({!erased_into_storage_ids}). *)
let erased_into_storage_tparam ~params body =
  let stored = erased_into_storage_ids body in
  if Id.Set.is_empty stored then fun _ -> false
  else fun id ->
    let names (t : ty) =
      match t with
      | Variable (Index (_, Some n) | Named n) | Named (n, _) -> Id.equal n id
      | External (n, _) -> String.equal n (Id.to_string id)
      | _ -> false
    in
    List.exists (fun (pid, ty) -> Id.Set.mem pid stored && Cpp_ir.Children.exists_type names ty) params

(** Whether a callable constraint over [dom] and [cod] states nothing a caller
    can be held to: a rank-2 callback's result, or an argument that is itself
    a callable, is [std::any] standing in for a type the body chooses. *)
let constraint_is_vacuous (dom : ty list) (cod : ty) =
  List.exists
    (fun t -> Cpp_ir.Children.exists_type (function Any | Obligation Opaque_type -> true | _ -> false) t)
    (cod :: List.filter (fun (t : ty) -> match t with Function _ -> true | _ -> false) dom)

(** The invocations [body] performs of the callable parameter of template
    type [tparam], whose signature types its arguments [dom]; [None] when a
    call cannot be read exactly.

    An argument's category is read off its syntax and the declaration of the
    name it reads: a variable is an lvalue, [const] when its declaration says
    so (a [const] reference, a structured binding, a borrowed match's
    fields); a [std::move] is an xvalue; a call, a construction, a literal
    other than a string is a prvalue.  The callable itself is an lvalue,
    [const] once a by-copy lambda has captured it.  Anything else -- a
    dereference, a mapping's binding, a call under [if constexpr] -- makes
    the reading inexact. *)
let invocations ~params (body : stmt list) tparam (dom : ty list) =
  let exception Inexact in
  let callable ty =
    let rec strip : ty -> ty = function Reference (_, t) | Const t -> strip t | t -> t in
    tvar_is tparam (strip ty)
  in
  let callables = List.filter_map (fun (x, ty) -> if callable ty then Some x else None) params in
  let is_callable x = List.exists (Id.equal x) callables in
  let declared : ty -> Value_category.t option = function
    | Const _ | Reference (Lvalue, Const _) -> Some Const_lvalue
    | _ -> Some Mutable_lvalue
  in
  let bind env x c = Id.Map.add x c env in
  let constify = Id.Map.map (Option.map (function Value_category.Mutable_lvalue -> Value_category.Const_lvalue | c -> c)) in
  let rec category env : expr -> Value_category.t option = function
    | Local x -> ( try Id.Map.find x env with Not_found -> None)
    | Move _ -> Some Xvalue
    | Access (Dot, (Local _ as o), _) | Member ((Local _ as o), _) -> category env o
    | Call _ | Aggregate _ | Local_aggregate _ | Lambda _
    | Literal (Uint63 _ | Int _ | Bool _ | Float _ | Null_pointer)
    | Binary _ | Converting_construct _ | Enum_value _ ->
      Some Prvalue
    | _ -> None
  in
  let found = ref [] in
  let record inv = if not (List.mem inv !found) then found := inv :: !found in
  let rec mentions_expr (e : expr) =
    (match e with Local x when is_callable x -> raise_notrace Exit | _ -> ());
    iter_expr ~expr:mentions_expr ~stmts:(List.iter mentions_stmt) e
  and mentions_stmt s = iter_stmt ~expr:mentions_expr ~stmts:(List.iter mentions_stmt) s in
  let mentions_any f =
    try
      f ();
      false
    with Exit -> true
  in
  let rec expr env (e : expr) =
    ( match e with
    | Call (_, Local f, args) when is_callable f ->
      let callee = match Id.Map.find_opt f env with Some (Some c) -> c | _ -> raise_notrace Inexact in
      if List.length args <> List.length dom then raise_notrace Inexact;
      let operand a t = match category env a with Some c -> (c, t) | None -> raise_notrace Inexact in
      record ({callable = callee; args = List.map2 operand args dom} : Cpp_ir.Lowered.phase Invocation.t)
    | _ -> () );
    match e with
    | Lambda l ->
      let env =
        match l.capture with
        | Stored | Written (By_copy _) -> constify env
        | Runs_in_place | Written (By_reference | Nothing) -> env
      in
      let env =
        List.fold_left (fun env (ty, x) -> match x with Some x -> bind env x (declared ty) | None -> env) env l.params
      in
      ignore (stmts env l.body)
    | Call (_, Local f, args) when is_callable f -> List.iter (expr env) args
    | _ -> iter_expr ~expr:(expr env) ~stmts:(fun b -> ignore (stmts env b)) e
  and stmts env = function
    | [] -> env
    | s :: rest -> stmts (stmt env s) rest
  and block env b = ignore (stmts env b)
  and stmt env (s : stmt) =
    match s with
    | Return eo ->
      Option.iter (expr env) eo;
      env
    | Expression e ->
      expr env e;
      env
    | Declare (x, ty, _) | Declare_value_initialized (x, ty) -> bind env x (declared ty)
    | Bind_variable (x, Declare (ty, _), e) ->
      expr env e;
      bind env x (declared ty)
    | Bind_variable (_, Existing, e) ->
      expr env e;
      env
    | Assign (l, r) ->
      expr env l;
      expr env r;
      env
    | Structured_binding (xs, e) ->
      expr env e;
      List.fold_left (fun env x -> bind env x (Some Value_category.Const_lvalue)) env xs
    | If i ->
      expr env i.condition;
      block env i.then_;
      block env i.else_;
      env
    | If_declaration i ->
      expr env i.init;
      let env' = bind env i.name (declared i.type_) in
      block env' i.then_;
      block env' i.else_;
      env
    | While (c, b) ->
      expr env c;
      block env b;
      env
    | Block b ->
      block env b;
      env
    | Switch w ->
      expr env w.scrutinee;
      List.iter (fun (_, b) -> block env b) w.branches;
      Option.iter (block env) w.default;
      env
    | Match (sc, branches, default) ->
      expr env sc.expr;
      let field : Value_category.t = if sc.owned then Mutable_lvalue else Const_lvalue in
      List.iter
        (fun (br : Cpp_ir.Lowered.phase Match.branch) ->
          let env =
            List.fold_left
              (fun env (fb : Cpp_ir.Lowered.phase Match.field_binding) -> bind env fb.name (Some field))
              env br.field_bindings
          in
          let env = match br.var with Some x -> bind env x (Some field) | None -> env in
          List.iter (expr env) br.extra_conditions;
          block env br.body )
        branches;
      Option.iter (block env) default;
      env
    | Throw _ | Foreign_text _ | Comment _ | Continue | Break | Local_struct _ | Local_type_alias _ -> env
    | _ ->
      if mentions_any (fun () -> mentions_stmt s) then raise_notrace Inexact;
      env
  in
  let env = List.fold_left (fun env (x, ty) -> bind env x (declared ty)) Id.Map.empty params in
  match ignore (stmts env body) with () -> Some (List.rev !found) | exception Inexact -> None

(** The parameters and statements of a declaration's body; empty for a
    declaration with none.  A variable's body returns its initialiser. *)
let rec body : decl -> (Id.t * ty) list * stmt list = function
  | Template (_, _, inner) -> body inner
  | Function {shape = Definition (params, b); _} -> (params, b)
  | Variable {init; _} -> ([], [Return (Some init)])
  | _ -> ([], [])

(** [ps] with each {!Cpp_ir.Grammar.Parameter_kind.Callable_declared}
    settled against the value parameters [params] and the statements [body]
    that use them, by the three rules of [cpp_constraints.mli]. *)
let settle_parameters ~params body (ps : parameters) : parameters =
  let stored = erased_into_storage_tparam ~params body in
  List.map
    (fun (((k : Cpp_ir.Lowered.phase Parameter_kind.t), id) as p) ->
      match k with
      | Callable_declared _ when stored id -> (Parameter_kind.Typename, id)
      | Callable_declared (dom, cod) when constraint_is_vacuous dom cod -> (Typename, id)
      | Callable_declared (dom, cod) -> (
        match invocations ~params body id dom with
        | Some (_ :: _ as invs) -> (Invocable (invs, cod), id)
        | Some [] | None -> (Typename, id) )
      | _ -> p )
    ps

let settle (d : decl) : decl =
  (* A position with no body to read states no call. *)
  let bodiless = settle_parameters ~params:[] [] in
  let settle_method (m : Cpp_ir.Lowered.phase Method.t) =
    {m with type_params = settle_parameters ~params:m.params m.body m.type_params}
  in
  let rec field ((f, vis, tag) : Cpp_ir.Lowered.phase Field.member) : Cpp_ir.Lowered.phase Field.member =
    let f : Cpp_ir.Lowered.phase Field.t =
      match f with
      | Method m -> Method (settle_method m)
      | Out_of_line_declaration (Method m) -> Out_of_line_declaration (Method (settle_method m))
      | Constructor c ->
        let inits = List.map (fun (_, e) -> Stmt.Expression e) c.inits in
        Constructor {c with type_params = settle_parameters ~params:c.params (inits @ c.body) c.type_params}
      | Nested_struct (id, fs) -> Nested_struct (id, List.map field fs)
      | Nested_type_alias (ps, id, ty) -> Nested_type_alias (bodiless ps, id, ty)
      | f -> f
    in
    (f, vis, tag)
  in
  let struct_ (s : Cpp_ir.Lowered.phase Struct.t) =
    {s with type_params = bodiless s.type_params; fields = List.map field s.fields}
  in
  let rec go : decl -> decl = function
    | Template (ps, c, d) ->
      let params, b = body d in
      Template (settle_parameters ~params b ps, c, go d)
    | Namespace (w, ds) -> Namespace (w, List.map go ds)
    | Struct s -> Struct (struct_ s)
    | Merged_struct_members s -> Merged_struct_members (struct_ s)
    | Struct_forward_declaration (ps, r) -> Struct_forward_declaration (bodiless ps, r)
    | Enum e -> Enum {e with type_params = bodiless e.type_params}
    | Member_definition m ->
      let member : Cpp_ir.Lowered.phase Out_of_line.t =
        match m.member with Method f -> Method (settle_method f) | Destructor _ as d -> d
      in
      Member_definition {m with type_params = bodiless m.type_params; member}
    | d -> d
  in
  go d
