(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** One level of structural rewriting: a node rebuilt from its rewritten
    children, the rewriting of each child left to the caller, who decides
    whether to descend.

    Children are rewritten in a fixed order, which a rewriter with effects
    -- one numbering what it lifts out, say -- sees: the arguments of a call
    from last to first and then the callee; any other list of expressions
    from first to last, before the expression they hang off; of two or
    three operands, the last first. *)

open Grammar

(** What a rewrite does with each child.  [stmts] rewrites a statement
    list: a block, a branch, a body. *)
type 'p t = {
  expr : 'p Expr.t -> 'p Expr.t;
  stmt : 'p Stmt.t -> 'p Stmt.t;
  stmts : 'p Stmt.t list -> 'p Stmt.t list;
  type_ : 'p Type.t -> 'p Type.t;
}

(** A rewrite whose statement lists are rewritten statement by statement,
    unless [stmts] says otherwise. *)
let make ?stmts ~expr ~stmt ~type_ () = {expr; stmt; type_; stmts = (match stmts with Some f -> f | None -> List.map stmt)}

let list = List.map
let opt = Option.map
let typed m ps = list (fun (t, x) -> (m.type_ t, x)) ps
let fields m ps = list (fun (x, t) -> (x, m.type_ t)) ps

(* The arguments of a call, last first. *)
let arguments m args = List.rev (list m.expr (List.rev args))

let foreign m (f : 'p Foreign.t) : 'p Foreign.t =
  let yields = opt m.type_ f.yields in
  let values = list m.expr f.values in
  let types = list m.type_ f.types in
  {f with types; values; yields}

let template_parameters : type p. p t -> p Template.parameters -> p Template.parameters =
 fun m ps ->
  list
    (fun ((k : p Parameter_kind.t), x) ->
      let k : p Parameter_kind.t =
        match k with
        | Typename_default t -> Typename_default (m.type_ t)
        | Callable_declared (dom, cod) -> Callable_declared (list m.type_ dom, m.type_ cod)
        | Invocable (invs, cod) ->
          Invocable
            (list (fun (i : p Invocation.t) -> {i with args = list (fun (c, t) -> (c, m.type_ t)) i.args}) invs, m.type_ cod)
        | Concept (r, ts) -> Concept (r, list m.type_ ts)
        | Typename | Template _ -> k
      in
      (k, x) )
    ps

let lambda m (l : 'p Lambda.t) : 'p Lambda.t =
  let body = m.stmts l.body in
  let return_type = opt m.type_ l.return_type in
  let params = typed m l.params in
  {l with params; return_type; body}

(** [expr m e] is [e] with each child rewritten by [m]. *)
let expr : type p. p t -> p Expr.t -> p Expr.t =
 fun m e ->
  let ty = m.type_ and ex = m.expr in
  match e with
  | Local _ | Literal _ | This | Projection_value _ | Enum_value _ | In_place | In_place_index _ | Numeral _
  | Foreign_text _ | Runtime _ ->
    e
  | Entity (r, ts, c) ->
    let c = opt (fun (c : p Foreign.custom) -> {c with custom_yields = opt ty c.custom_yields}) c in
    Entity (r, list ty ts, c)
  | Call (s, f, args) ->
    let yields : p Call.result = match s.yields with Yields t -> Yields (ty t) | Untyped -> Untyped in
    let params : p Call.params = match s.params with Types ts -> Types (list ty ts) | Unknown -> Unknown in
    let args = arguments m args in
    let f = ex f in
    Call ({s with yields; params}, f, args)
  | Converting_construct (t, es) ->
    let es = list ex es in
    Converting_construct (ty t, es)
  | Box (t, e) ->
    let e = ex e in
    Box (ty t, e)
  | Dereference e -> Dereference (ex e)
  | Move e -> Move (ex e)
  | Forward (t, e) ->
    let e = ex e in
    Forward (ty t, e)
  | Lambda l -> Lambda (lambda m l)
  | Suspend (t, e) ->
    let e = ex e in
    Suspend (ty t, e)
  | Allocate (k, t) -> Allocate (k, ty t)
  | Aggregate a ->
    let values = list ex a.values in
    Aggregate {a with type_args = list ty a.type_args; values}
  | Local_aggregate a ->
    let values = list ex a.values in
    Local_aggregate {a with type_args = list ty a.type_args; values}
  | Member (e, x) -> Member (ex e, x)
  | Project (e, r, t) ->
    let t = opt ty t in
    Project (ex e, r, t)
  | Persistent_array (es, d) ->
    let d = ex d in
    let es = Array.map ex es in
    Persistent_array (es, d)
  | Requires q ->
    let type_requirements = list ty q.type_requirements in
    let constraints =
      list
        (fun (e, c) ->
          let c = ex c in
          (ex e, c) )
        q.constraints
    in
    let params = typed m q.params in
    Requires {params; constraints; type_requirements}
  | Concept_application (c, s, ts) -> Concept_application (c, s, list ty ts)
  | Shared_from_this t -> Shared_from_this (ty t)
  | Access (a, e, x) -> Access (a, ex e, x)
  | Access_call (a, e, x, es) ->
    let es = list ex es in
    Access_call (a, ex e, x, es)
  | Method_call c ->
    let args = list ex c.args in
    let type_args = list ty c.type_args in
    let receiver = ex c.receiver in
    Method_call {c with receiver; type_args; args}
  | Method_value v -> Method_value {v with params = list (opt ty) v.params; type_args = list ty v.type_args}
  | Projection p ->
    let args = list ex p.args in
    Projection {p with record = ex p.record; args}
  | Scope (e, x, ts) ->
    let ts = list ty ts in
    Scope (ex e, x, ts)
  | Type_member (t, x) -> Type_member (ty t, x)
  | Convertible_to t -> Convertible_to (ty t)
  | Abort (s, t) -> Abort (s, ty t)
  | Braced es -> Braced (list ex es)
  | Variant_get (t, e) ->
    let e = opt ex e in
    Variant_get (ty t, e)
  | Holds_alternative t -> Holds_alternative (ty t)
  | Declval t -> Declval (ty t)
  | Type_name t -> Type_name (ty t)
  | Binary (o, a, b) ->
    let b = ex b in
    Binary (o, ex a, b)
  | Conditional (c, a, b) ->
    let b = ex b in
    let a = ex a in
    Conditional (ex c, a, b)
  | Unary (o, e) -> Unary (o, ex e)
  | Any_cast (t, e) ->
    let e = ex e in
    Any_cast (ty t, e)
  | Tolerant_any_cast (t, e) ->
    let e = ex e in
    Tolerant_any_cast (ty t, e)
  | Unbox (u, e) ->
    let u : p Unbox.t = match u with To t -> To (ty t) | Or_keep t -> Or_keep (ty t) | List (a, b) -> List (ty a, ty b) in
    Unbox (u, ex e)
  | Convert (t, e) ->
    let e = ex e in
    Convert (ty t, e)
  | Erase_callable (s, e) ->
    let e = ex e in
    let s : p Erase_shape.t = match s with Boxed_whole -> Boxed_whole | At_signature t -> At_signature (ty t) in
    Erase_callable (s, e)
  | Erased_call (f, a) ->
    let a = ex a in
    Erased_call (ex f, a)
  | Tolerant_call (f, es) ->
    let es = list ex es in
    Tolerant_call (ex f, es)
  | Function_value e -> Function_value (ex e)
  | Container_cast (t, e, b) ->
    let e = ex e in
    Container_cast (ty t, e, b)
  | Variant_get_if (t, e) ->
    let e = ex e in
    Variant_get_if (ty t, e)
  | Foreign (u, f) -> Foreign (u, foreign m f)

(** [stmt m s] is [s] with each child rewritten by [m]. *)
let stmt : type p. p t -> p Stmt.t -> p Stmt.t =
 fun m s ->
  let ty = m.type_ and ex = m.expr and body = m.stmts in
  match s with
  | Return None | Throw _ | Assert _ | Foreign_text _ | Comment _ | Continue | Break -> s
  | Return (Some e) -> Return (Some (ex e))
  | Declare (x, t, b) -> Declare (x, ty t, b)
  | Bind_variable (x, b, e) ->
    let b : p Binding.t =
      match b with Declare (t, c) -> Declare (ty t, c) | Declare_static t -> Declare_static (ty t) | Existing -> Existing
    in
    Bind_variable (x, b, ex e)
  | Expression e -> Expression (ex e)
  | Custom_match c ->
    let branches =
      list
        (fun (b : p Custom_match.branch) : p Custom_match.branch ->
          let b_body = body b.body in
          let b_type = ty b.type_ in
          {params = list (fun (p : p Custom_match.param) -> {p with type_ = ty p.type_}) b.params; type_ = b_type; body = b_body} )
        c.branches
    in
    let type_args = list ty c.type_args in
    let scrutinee = ex c.scrutinee in
    Custom_match {c with return_type = ty c.return_type; scrutinee; type_args; branches}
  | Switch w ->
    let default = opt body w.default in
    let branches = list (fun (x, ss) -> (x, body ss)) w.branches in
    Switch {w with scrutinee = ex w.scrutinee; branches; default}
  | If i ->
    let else_ = body i.else_ in
    let then_ = body i.then_ in
    If {condition = ex i.condition; then_; else_}
  | If_constexpr i ->
    let (Convertible (a, b)) = i.test in
    let else_ = body i.else_ in
    let then_ = body i.then_ in
    If_constexpr {test = Convertible (ty a, ty b); then_; else_}
  | If_declaration i ->
    let else_ = body i.else_ in
    let then_ = body i.then_ in
    let init = ex i.init in
    If_declaration {i with type_ = ty i.type_; init; then_; else_}
  | Local_struct (x, fs) -> Local_struct (x, fields m fs)
  | Local_type_alias (x, t) -> Local_type_alias (x, ty t)
  | Structured_binding (xs, e) -> Structured_binding (xs, ex e)
  | Declare_value_initialized (x, t) -> Declare_value_initialized (x, ty t)
  | Assign (l, r) ->
    let r = ex r in
    Assign (ex l, r)
  | For_range (x, e, ss) ->
    let ss = body ss in
    For_range (x, ex e, ss)
  | While (c, ss) ->
    let ss = body ss in
    While (ex c, ss)
  | Block ss -> Block (body ss)
  | Match (sc, bs, d) ->
    let d = opt body d in
    let bs =
      list
        (fun (b : p Match.branch) : p Match.branch ->
          let b_body = body b.body in
          let extra_conditions = list ex b.extra_conditions in
          let field_bindings = list (fun (f : p Match.field_binding) -> {f with type_ = ty f.type_}) b.field_bindings in
          {b with ctor_type = ty b.ctor_type; field_bindings; extra_conditions; body = b_body} )
        bs
    in
    Match ({sc with expr = ex sc.expr}, bs, d)
  | Foreign_block b ->
    let type_args = list ty b.type_args in
    let values = list ex b.values in
    Foreign_block {b with result_type = ty b.result_type; values; type_args}

let method_ m (f : 'p Method.t) : 'p Method.t =
  let body = m.stmts f.body in
  let params = fields m f.params in
  let return_type = m.type_ f.return_type in
  {f with type_params = template_parameters m f.type_params; return_type; params; body}

let out_of_line m : 'p Out_of_line.t -> 'p Out_of_line.t = function
  | Method f -> Method (method_ m f)
  | Destructor ss -> Destructor (m.stmts ss)

(** [member m f] is the struct member [f] with each child rewritten by
    [m]; a nested struct's members are rewritten as members. *)
let rec member m ((f, v, s) : 'p Field.member) : 'p Field.member =
  let f : 'p Field.t =
    match f with
    | Data (x, t) -> Data (x, m.type_ t)
    | Entity_data (r, t) -> Entity_data (r, m.type_ t)
    | Method f -> Method (method_ m f)
    | Constructor c ->
      let body = m.stmts c.body in
      let inits = list (fun (x, e) -> (x, m.expr e)) c.inits in
      let params = fields m c.params in
      Constructor {c with type_params = template_parameters m c.type_params; params; inits; body}
    | Destructor ss -> Destructor (m.stmts ss)
    | Nested_struct (x, ms) -> Nested_struct (x, list (member m) ms)
    | Deferred_struct d ->
      let fields_ = fields m d.fields in
      Deferred_struct {d with selves = fields m d.selves; fields = fields_}
    | Nested_type_alias (ps, x, t) ->
      let t = m.type_ t in
      Nested_type_alias (template_parameters m ps, x, t)
    | Out_of_line_declaration o -> Out_of_line_declaration (out_of_line m o)
    | Deleted_default_constructor | Defaulted_special_members -> f
  in
  (f, v, s)

let struct_ m (s : 'p Struct.t) : 'p Struct.t =
  let constraint_ = opt m.expr s.constraint_ in
  let fields = list (member m) s.fields in
  {s with type_params = template_parameters m s.type_params; fields; constraint_}

(** [decl m d] is [d] with each child rewritten by [m]; a template's and a
    namespace's declarations, and a struct's members, are rewritten down to
    their children. *)
let rec decl m : 'p Decl.t -> 'p Decl.t = function
  | Template (ps, c, d) ->
    let d = decl m d in
    let c = opt m.expr c in
    Template (template_parameters m ps, c, d)
  | Namespace (w, ds) -> Namespace (w, list (decl m) ds)
  | Function f ->
    let entry (r, ts) = (r, list m.type_ ts) in
    let shape : 'p Function.shape =
      match f.shape with
      | Definition (ps, b) ->
        let b = m.stmts b in
        Definition (fields m ps, b)
      | Declaration ps -> Declaration (fields m ps)
    in
    let return_type = m.type_ f.return_type in
    let inner = list entry f.path.inner in
    Function {f with path = {outer = entry f.path.outer; inner}; return_type; shape}
  | Struct s -> Struct (struct_ m s)
  | Merged_struct_members s -> Merged_struct_members (struct_ m s)
  | Variable v ->
    let init = m.expr v.init in
    Variable {v with type_ = m.type_ v.type_; init}
  | Concept (r, e) -> Concept (r, m.expr e)
  | Static_assert (e, s) -> Static_assert (m.expr e, s)
  | Type_alias a ->
    let rhs = opt m.type_ a.rhs in
    Type_alias {a with type_params = template_parameters m a.type_params; rhs}
  | Struct_forward_declaration (ps, r) -> Struct_forward_declaration (template_parameters m ps, r)
  | Member_definition d ->
    let member = out_of_line m d.member in
    Member_definition {d with type_params = template_parameters m d.type_params; member}
  | Enum e -> Enum {e with type_params = template_parameters m e.type_params}
