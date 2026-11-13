(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A lowered value that owes resolution nothing, at the resolved phase.

    Each function rebuilds its argument constructor for constructor; a form
    only a lowered value may hold ({!Grammar.lowered}) has no resolved
    counterpart, and raises {!Owed} naming it. *)

open Grammar

type l = lowered
type r = resolved

(** The lowered-only form a value still holds. *)
exception Owed of string

let owed form = raise_notrace (Owed form)
let list = List.map
let opt = Option.map

(** [type_ t] is [t] at the resolved phase; raises {!Owed} at an
    obligation. *)
let rec type_ : l Type.t -> r Type.t = function
  | Variable v -> Variable v
  | Instance (x, c) -> Instance (x, c)
  | Promoted_member x -> Promoted_member x
  | Named (x, ts) -> Named (x, list type_ ts)
  | External (s, ts) -> External (s, list type_ ts)
  | Entity_application (r, ts, es) -> Entity_application (r, list type_ ts, list expr es)
  | Function (ds, c) -> Function (list type_ ds, type_ c)
  | Const t -> Const (type_ t)
  | In_namespace (r, t) -> In_namespace (r, type_ t)
  | Member (t, x) -> Member (type_ t, x)
  | Apply (t, ts) -> Apply (type_ t, list type_ ts)
  | Reference (k, t) -> Reference (k, type_ t)
  | Erased k -> Erased k
  | Pointer t -> Pointer (type_ t)
  | Variant (s, ts) -> Variant (s, list type_ ts)
  | Shared_pointer t -> Shared_pointer (type_ t)
  | Void -> Void
  | Any -> Any
  | Type_constructor t -> Type_constructor (type_ t)
  | Carrier_parameter -> Carrier_parameter
  | Auto -> Auto
  | Decay t -> Decay (type_ t)
  | Non_deduced t -> Non_deduced (type_ t)
  | Rebind (f, x) -> Rebind (type_ f, type_ x)
  | Type_of e -> Type_of (expr e)
  | Decltype_auto -> Decltype_auto
  | Foreign f -> Foreign (foreign f)
  | Obligation Unresolved_type -> owed "an unresolved type"
  | Obligation Opaque_type -> owed "an opaque type"
  | Obligation _ -> owed "a type obligation"

and foreign (f : l Foreign.t) : r Foreign.t =
  {custom = f.custom; types = list type_ f.types; values = list expr f.values; yields = opt type_ f.yields; pieces = f.pieces}

and custom (c : l Foreign.custom) : r Foreign.custom = {inline = c.inline; custom_yields = opt type_ c.custom_yields}

and signature (s : l Call.signature) : r Call.signature =
  { yields = (match s.yields with Yields t -> Yields (type_ t) | Untyped -> Untyped);
    params = (match s.params with Types ts -> Types (list type_ ts) | Unknown -> Unknown);
    constructs = s.constructs;
    occurrence = s.occurrence }

and capture : l Capture.t -> r Capture.t = function
  | Written w -> Written w
  | Runs_in_place -> owed "a capture that runs in place"
  | Stored -> owed "a stored capture"

and lambda (l : l Lambda.t) : r Lambda.t =
  { params = list (fun (t, x) -> (type_ t, x)) l.params;
    type_params = l.type_params;
    return_type = opt type_ l.return_type;
    body = stmts l.body;
    capture = capture l.capture;
    moved = l.moved;
    binders = l.binders;
    fixpoint = l.fixpoint }

and aggregate : 'n. ('n, l) Aggregate.t -> ('n, r) Aggregate.t =
 fun a -> {struct_ = a.struct_; type_args = list type_ a.type_args; values = list expr a.values}

(** [expr e] is [e] at the resolved phase; raises {!Owed} at an obligation,
    a suspension, or an undecided capture. *)
and expr : l Expr.t -> r Expr.t = function
  | Local x -> Local x
  | Entity (r, ts, c) -> Entity (r, list type_ ts, opt custom c)
  | Call (s, f, args) -> Call (signature s, expr f, list expr args)
  | Converting_construct (t, es) -> Converting_construct (type_ t, list expr es)
  | Box (t, e) -> Box (type_ t, expr e)
  | Dereference e -> Dereference (expr e)
  | Move e -> Move (expr e)
  | Forward (t, e) -> Forward (type_ t, expr e)
  | Lambda l -> Lambda (lambda l)
  | Suspend _ -> owed "a suspended constructor"
  | Allocate (k, t) -> Allocate (k, type_ t)
  | Aggregate a -> Aggregate (aggregate a)
  | Local_aggregate a -> Local_aggregate (aggregate a)
  | Member (e, x) -> Member (expr e, x)
  | Project (e, r, t) -> Project (expr e, r, opt type_ t)
  | Literal l -> Literal l
  | Persistent_array (es, d) -> Persistent_array (Array.map expr es, expr d)
  | Requires q ->
    Requires
      { params = list (fun (t, x) -> (type_ t, x)) q.params;
        constraints = list (fun (e, c) -> (expr e, expr c)) q.constraints;
        type_requirements = list type_ q.type_requirements }
  | Concept_application (c, s, ts) -> Concept_application (c, s, list type_ ts)
  | This -> This
  | Shared_from_this t -> Shared_from_this (type_ t)
  | Access (a, e, x) -> Access (a, expr e, x)
  | Access_call (a, e, x, es) -> Access_call (a, expr e, x, list expr es)
  | Method_call m ->
    Method_call
      { method_ = m.method_;
        access = m.access;
        receiver = expr m.receiver;
        type_args = list type_ m.type_args;
        args = list expr m.args }
  | Method_value m ->
    Method_value
      { method_ = m.method_;
        access = m.access;
        receiver = m.receiver;
        params = list (opt type_) m.params;
        type_args = list type_ m.type_args }
  | Projection p -> Projection {projection = p.projection; record = expr p.record; args = list expr p.args}
  | Projection_value r -> Projection_value r
  | Scope (e, x, ts) -> Scope (expr e, x, list type_ ts)
  | Type_member (t, x) -> Type_member (type_ t, x)
  | Convertible_to t -> Convertible_to (type_ t)
  | Abort (s, t) -> Abort (s, type_ t)
  | Enum_value (r, x) -> Enum_value (r, x)
  | In_place -> In_place
  | In_place_index i -> In_place_index i
  | Braced es -> Braced (list expr es)
  | Variant_get (t, e) -> Variant_get (type_ t, opt expr e)
  | Holds_alternative t -> Holds_alternative (type_ t)
  | Declval t -> Declval (type_ t)
  | Type_name t -> Type_name (type_ t)
  | Numeral (r, n) -> Numeral (r, n)
  | Foreign_text s -> Foreign_text s
  | Runtime h -> Runtime h
  | Binary (o, a, b) -> Binary (o, expr a, expr b)
  | Conditional (c, a, b) -> Conditional (expr c, expr a, expr b)
  | Unary (o, e) -> Unary (o, expr e)
  | Any_cast (t, e) -> Any_cast (type_ t, expr e)
  | Tolerant_any_cast (t, e) -> Tolerant_any_cast (type_ t, expr e)
  | Unbox (u, e) ->
    let u : r Unbox.t =
      match u with To t -> To (type_ t) | Or_keep t -> Or_keep (type_ t) | List (a, b) -> List (type_ a, type_ b)
    in
    Unbox (u, expr e)
  | Convert (t, e) -> Convert (type_ t, expr e)
  | Erase_callable (s, e) ->
    Erase_callable ((match s with Boxed_whole -> Boxed_whole | At_signature t -> At_signature (type_ t)), expr e)
  | Erased_call (f, a) -> Erased_call (expr f, expr a)
  | Tolerant_call (f, es) -> Tolerant_call (expr f, list expr es)
  | Function_value e -> Function_value (expr e)
  | Container_cast (t, e, b) -> Container_cast (type_ t, expr e, b)
  | Variant_get_if (t, e) -> Variant_get_if (type_ t, expr e)
  | Foreign (u, f) -> Foreign (u, foreign f)

and binding : l Binding.t -> r Binding.t = function
  | Declare (t, b) -> Declare (type_ t, b)
  | Existing -> Existing
  | Declare_static t -> Declare_static (type_ t)

and custom_match (m : l Custom_match.t) : r Custom_match.t =
  let param (p : l Custom_match.param) : r Custom_match.param = {name = p.name; type_ = type_ p.type_; binder = p.binder} in
  { return_type = type_ m.return_type;
    scrutinee = expr m.scrutinee;
    type_args = list type_ m.type_args;
    branches =
      list (fun (b : l Custom_match.branch) : r Custom_match.branch ->
        {params = list param b.params; type_ = type_ b.type_; body = stmts b.body}) m.branches;
    template = m.template;
    inductive = m.inductive;
    hold = m.hold;
    pieces = (match m.pieces with Instantiated ps -> Instantiated ps | Uninstantiated -> owed "an uninstantiated custom match") }

and match_branch (b : l Match.branch) : r Match.branch =
  let field (f : l Match.field_binding) : r Match.field_binding =
    {name = f.name; type_ = type_ f.type_; used = f.used; binder = f.binder}
  in
  { ctor_type = type_ b.ctor_type;
    var = b.var;
    field_bindings = list field b.field_bindings;
    extra_conditions = list expr b.extra_conditions;
    body = stmts b.body }

and stmts ss = list stmt ss

(** [stmt s] is [s] at the resolved phase; raises {!Owed} at an
    uninstantiated mapping block or match template. *)
and stmt : l Stmt.t -> r Stmt.t = function
  | Return e -> Return (opt expr e)
  | Declare (x, t, b) -> Declare (x, type_ t, b)
  | Bind_variable (x, b, e) -> Bind_variable (x, binding b, expr e)
  | Expression e -> Expression (expr e)
  | Custom_match m -> Custom_match (custom_match m)
  | Throw s -> Throw s
  | Switch s ->
    Switch
      { scrutinee = expr s.scrutinee;
        enum = s.enum;
        branches = list (fun (x, ss) -> (x, stmts ss)) s.branches;
        default = opt stmts s.default }
  | Assert p -> Assert p
  | If s -> If {condition = expr s.condition; then_ = stmts s.then_; else_ = stmts s.else_}
  | If_constexpr s ->
    let (Convertible (a, b)) = s.test in
    If_constexpr {test = Convertible (type_ a, type_ b); then_ = stmts s.then_; else_ = stmts s.else_}
  | If_declaration s ->
    If_declaration {name = s.name; type_ = type_ s.type_; init = expr s.init; then_ = stmts s.then_; else_ = stmts s.else_}
  | Foreign_text s -> Foreign_text s
  | Comment s -> Comment s
  | Local_struct (x, fs) -> Local_struct (x, list (fun (f, t) -> (f, type_ t)) fs)
  | Local_type_alias (x, t) -> Local_type_alias (x, type_ t)
  | Structured_binding (xs, e) -> Structured_binding (xs, expr e)
  | Declare_value_initialized (x, t) -> Declare_value_initialized (x, type_ t)
  | Assign (a, b) -> Assign (expr a, expr b)
  | For_range (x, e, ss) -> For_range (x, expr e, stmts ss)
  | While (c, ss) -> While (expr c, stmts ss)
  | Block ss -> Block (stmts ss)
  | Continue -> Continue
  | Break -> Break
  | Match (sc, bs, d) ->
    Match
      ( {expr = expr sc.expr; access = sc.access; owned = sc.owned; flat = sc.flat},
        list match_branch bs,
        opt stmts d )
  | Foreign_block _ -> owed "an uninstantiated mapping block"

let parameter_kind : l Parameter_kind.t -> r Parameter_kind.t = function
  | Typename -> Typename
  | Typename_default t -> Typename_default (type_ t)
  | Template n -> Template n
  | Callable_declared _ -> owed "a callable parameter's declared constraint"
  | Invocable (is, t) ->
    Invocable (list (fun (i : l Invocation.t) : r Invocation.t -> {callable = i.callable; args = list (fun (c, t) -> (c, type_ t)) i.args}) is, type_ t)
  | Concept (r, ts) -> Concept (r, list type_ ts)

let parameters ps : r Template.parameters = list (fun (k, x) -> (parameter_kind k, x)) ps

let constexpr : l Constexpr.t -> r Constexpr.t = function
  | Eligible -> Eligible
  | Ineligible -> Ineligible
  | Undecided -> owed "an undecided constexpr"

let typed ps = list (fun (x, t) -> (x, type_ t)) ps

let method_ (m : l Method.t) : r Method.t =
  { name = m.name;
    globref = m.globref;
    type_params = parameters m.type_params;
    return_type = type_ m.return_type;
    params = typed m.params;
    body = stmts m.body;
    receiver = m.receiver;
    is_inline = m.is_inline;
    no_pure = m.no_pure;
    constexpr = constexpr m.constexpr;
    is_noexcept = m.is_noexcept;
    is_conversion = m.is_conversion;
    binders = m.binders;
    receiver_binder = m.receiver_binder;
    loop = m.loop }

let out_of_line : l Out_of_line.t -> r Out_of_line.t = function
  | Method m -> Method (method_ m)
  | Destructor ss -> Destructor (stmts ss)

let rec field : l Field.t -> r Field.t = function
  | Data (x, t) -> Data (x, type_ t)
  | Entity_data (r, t) -> Entity_data (r, type_ t)
  | Method m -> Method (method_ m)
  | Constructor c ->
    Constructor
      { type_params = parameters c.type_params;
        params = typed c.params;
        inits = list (fun (x, e) -> (x, expr e)) c.inits;
        body = stmts c.body;
        explicit = c.explicit;
        noexcept = c.noexcept }
  | Destructor ss -> Destructor (stmts ss)
  | Nested_struct (x, ms) -> Nested_struct (x, list member ms)
  | Deferred_struct d -> Deferred_struct {name = d.name; selves = typed d.selves; fields = typed d.fields}
  | Nested_type_alias (ps, x, t) -> Nested_type_alias (parameters ps, x, type_ t)
  | Out_of_line_declaration o -> Out_of_line_declaration (out_of_line o)
  | Deleted_default_constructor -> Deleted_default_constructor
  | Defaulted_special_members -> Defaulted_special_members

and member (f, v, s) : r Field.member = (field f, v, s)

let struct_ (s : l Struct.t) : r Struct.t =
  { ref_ = s.ref_;
    fields = list member s.fields;
    type_params = parameters s.type_params;
    constraint_ = opt expr s.constraint_;
    needs_shared_from_this = s.needs_shared_from_this }

let path_entry (r, ts) = (r, list type_ ts)

let function_ (f : l Function.t) : r Function.t =
  { path = {outer = path_entry f.path.outer; inner = list path_entry f.path.inner};
    return_type = type_ f.return_type;
    no_pure = f.no_pure;
    constexpr = constexpr f.constexpr;
    shape =
      ( match f.shape with
      | Definition (ps, body) -> Definition (typed ps, stmts body)
      | Declaration ps -> Declaration (list (fun (x, t) -> (x, type_ t)) ps) );
    binders = f.binders;
    loop = f.loop }

(** [decl d] is [d] at the resolved phase; raises {!Owed} also at a callable
    parameter's declared constraint or an undecided [constexpr]. *)
let rec decl : l Decl.t -> r Decl.t = function
  | Template (ps, c, d) -> Template (parameters ps, opt expr c, decl d)
  | Namespace (w, ds) -> Namespace (w, list decl ds)
  | Function f -> Function (function_ f)
  | Struct s -> Struct (struct_ s)
  | Variable v -> Variable {ref_ = v.ref_; type_ = type_ v.type_; init = expr v.init; constexpr = constexpr v.constexpr}
  | Concept (r, e) -> Concept (r, expr e)
  | Static_assert (e, m) -> Static_assert (expr e, m)
  | Type_alias a -> Type_alias {type_params = parameters a.type_params; name = a.name; rhs = opt type_ a.rhs; note = a.note}
  | Struct_forward_declaration (ps, r) -> Struct_forward_declaration (parameters ps, r)
  | Merged_struct_members s -> Merged_struct_members (struct_ s)
  | Member_definition m ->
    Member_definition {owner = m.owner; enclosing = m.enclosing; type_params = parameters m.type_params; member = out_of_line m.member}
  | Enum e -> Enum {ref_ = e.ref_; ctors = e.ctors; rocq_names = e.rocq_names; type_params = parameters e.type_params}
