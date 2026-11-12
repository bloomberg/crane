(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** One level of descent into CppIR: the expressions, statements and types a
    term holds directly, handed in the order they are written to the
    visitor's function for their family.  Nothing below a child is visited:
    the visitor recurses, or does not.

    Every child counts, written or not: a call's signature, a mapped
    global's [%result] type, a structured binding's field types.  A visitor
    that wants only what is written handles those nodes itself.  The types
    inside a type are not visited by these functions; {!type_children}
    lists them. *)

open Grammar

(** What a visit does with each child it finds. *)
type 'p visitor = {
  expr : 'p Expr.t -> unit;
  stmt : 'p Stmt.t -> unit;
  type_ : 'p Type.t -> unit;
}

let opt f = Option.iter f
let each f = List.iter f
let typed v ps = each (fun (t, _) -> v.type_ t) ps
let fields v ps = each (fun (_, t) -> v.type_ t) ps

(** The types a template parameter list holds: a default, a callable's
    constraint, a concept's further arguments. *)
let template_parameters : type p. p visitor -> p Template.parameters -> unit =
 fun v ps ->
  each
    (fun ((k : p Parameter_kind.t), _) ->
      match k with
      | Typename_default t -> v.type_ t
      | Callable_declared (dom, cod) ->
        each v.type_ dom;
        v.type_ cod
      | Invocable (invs, cod) ->
        each (fun (i : p Invocation.t) -> each (fun (_, t) -> v.type_ t) i.args) invs;
        v.type_ cod
      | Concept (_, ts) -> each v.type_ ts
      | Typename | Template _ -> () )
    ps

(** The children of a mapping instantiated at one use: its type arguments,
    value arguments and result type. *)
let foreign v (f : 'p Foreign.t) =
  each v.type_ f.types;
  each v.expr f.values;
  opt v.type_ f.yields

(** The children of an expression. *)
let expr : type p. p visitor -> p Expr.t -> unit =
 fun v e ->
  match e with
  | Local _ | Literal _ | This | Projection_value _ | Enum_value _ | In_place | In_place_index _ | Numeral _
  | Foreign_text _ | Runtime _ ->
    ()
  | Entity (_, ts, custom) ->
    each v.type_ ts;
    opt (fun (c : p Foreign.custom) -> opt v.type_ c.custom_yields) custom
  | Call (s, f, args) ->
    (match s.yields with Yields t -> v.type_ t | Untyped -> ());
    (match s.params with Types ts -> each v.type_ ts | Unknown -> ());
    v.expr f;
    each v.expr args
  | Converting_construct (t, es) ->
    v.type_ t;
    each v.expr es
  | Box (t, e) | Forward (t, e) | Any_cast (t, e) | Tolerant_any_cast (t, e) | Convert (t, e)
  | Container_cast (t, e, _) | Variant_get_if (t, e) ->
    v.type_ t;
    v.expr e
  | Suspend (t, e) ->
    v.type_ t;
    v.expr e
  | Dereference e | Move e | Member (e, _) | Access (_, e, _) | Function_value e -> v.expr e
  | Lambda l ->
    typed v l.params;
    opt v.type_ l.return_type;
    each v.stmt l.body
  | Allocate (_, t) | Shared_from_this t | Type_member (t, _) | Convertible_to t | Abort (_, t)
  | Holds_alternative t | Declval t | Type_name t ->
    v.type_ t
  | Aggregate a ->
    each v.type_ a.type_args;
    each v.expr a.values
  | Local_aggregate a ->
    each v.type_ a.type_args;
    each v.expr a.values
  | Project (e, _, t) ->
    v.expr e;
    opt v.type_ t
  | Persistent_array (es, d) ->
    Array.iter v.expr es;
    v.expr d
  | Requires r ->
    typed v r.params;
    each
      (fun (e, c) ->
        v.expr e;
        v.expr c )
      r.constraints;
    each v.type_ r.type_requirements
  | Concept_application (_, _, ts) -> each v.type_ ts
  | Access_call (_, e, _, es) ->
    v.expr e;
    each v.expr es
  | Method_call m ->
    v.expr m.receiver;
    each v.type_ m.type_args;
    each v.expr m.args
  | Method_value m ->
    each (opt v.type_) m.params;
    each v.type_ m.type_args
  | Projection p ->
    v.expr p.record;
    each v.expr p.args
  | Scope (e, _, ts) ->
    v.expr e;
    each v.type_ ts
  | Braced es -> each v.expr es
  | Variant_get (t, e) ->
    v.type_ t;
    opt v.expr e
  | Binary (_, a, b) | Erased_call (a, b) ->
    v.expr a;
    v.expr b
  | Conditional (c, a, b) ->
    v.expr c;
    v.expr a;
    v.expr b
  | Unary (_, e) -> v.expr e
  | Unbox (u, e) ->
    ( match u with
    | To t | Or_keep t -> v.type_ t
    | List (l, f) ->
      v.type_ l;
      v.type_ f );
    v.expr e
  | Erase_callable (s, e) ->
    (match s with At_signature t -> v.type_ t | Boxed_whole -> ());
    v.expr e
  | Tolerant_call (f, es) ->
    v.expr f;
    each v.expr es
  | Foreign (_, f) -> foreign v f

(** The children of a statement. *)
let stmt : type p. p visitor -> p Stmt.t -> unit =
 fun v s ->
  let body = each v.stmt in
  match s with
  | Return e -> opt v.expr e
  | Declare (_, t, _) | Local_type_alias (_, t) | Declare_value_initialized (_, t) -> v.type_ t
  | Bind_variable (_, b, e) ->
    (match b with Declare (t, _) | Declare_static t -> v.type_ t | Existing -> ());
    v.expr e
  | Expression e | Structured_binding (_, e) -> v.expr e
  | Custom_match m ->
    v.type_ m.return_type;
    v.expr m.scrutinee;
    each v.type_ m.type_args;
    each
      (fun (b : p Custom_match.branch) ->
        each (fun (p : p Custom_match.param) -> v.type_ p.type_) b.params;
        v.type_ b.type_;
        body b.body )
      m.branches
  | Throw _ | Assert _ | Foreign_text _ | Comment _ | Continue | Break -> ()
  | Switch {scrutinee; branches; default; _} ->
    v.expr scrutinee;
    each (fun (_, ss) -> body ss) branches;
    opt body default
  | If {condition; then_; else_} ->
    v.expr condition;
    body then_;
    body else_
  | If_constexpr {test = Convertible (a, b); then_; else_} ->
    v.type_ a;
    v.type_ b;
    body then_;
    body else_
  | If_declaration {type_; init; then_; else_; _} ->
    v.type_ type_;
    v.expr init;
    body then_;
    body else_
  | Local_struct (_, fs) -> fields v fs
  | Assign (l, r) ->
    v.expr l;
    v.expr r
  | For_range (_, e, ss) | While (e, ss) ->
    v.expr e;
    body ss
  | Block ss -> body ss
  | Match (scrutinee, branches, default) ->
    v.expr scrutinee.expr;
    each
      (fun (b : p Match.branch) ->
        v.type_ b.ctor_type;
        each (fun (f : p Match.field_binding) -> v.type_ f.type_) b.field_bindings;
        each v.expr b.extra_conditions;
        body b.body )
      branches;
    opt body default
  | Foreign_block b ->
    v.type_ b.result_type;
    each v.expr b.values;
    each v.type_ b.type_args

(** The children of a member function: its template parameters, return
    type, parameter types and body. *)
let method_ v (m : 'p Method.t) =
  template_parameters v m.type_params;
  v.type_ m.return_type;
  fields v m.params;
  each v.stmt m.body

(** The children of a member that can be defined outside its struct. *)
let out_of_line v : 'p Out_of_line.t -> unit = function
  | Method m -> method_ v m
  | Destructor ss -> each v.stmt ss

(** The children of a struct member; a nested struct's members are visited
    as members, down to their children. *)
let rec member v ((f, _, _) : 'p Field.member) =
  match f with
  | Data (_, t) | Entity_data (_, t) -> v.type_ t
  | Method m -> method_ v m
  | Constructor c ->
    template_parameters v c.type_params;
    fields v c.params;
    each (fun (_, e) -> v.expr e) c.inits;
    each v.stmt c.body
  | Destructor ss -> each v.stmt ss
  | Nested_struct (_, ms) -> each (member v) ms
  | Deferred_struct d ->
    fields v d.selves;
    fields v d.fields
  | Nested_type_alias (ps, _, t) ->
    template_parameters v ps;
    v.type_ t
  | Out_of_line_declaration m -> out_of_line v m
  | Deleted_default_constructor | Defaulted_special_members -> ()

(** The children of a struct: its template parameters, its members down to
    their children, and its constraint. *)
let struct_ v (s : 'p Struct.t) =
  template_parameters v s.type_params;
  each (member v) s.fields;
  opt v.expr s.constraint_

(** The children of a declaration; a template's and a namespace's
    declarations, and a struct's members, are visited down to their
    children. *)
let rec decl v : 'p Decl.t -> unit = function
  | Template (ps, c, d) ->
    template_parameters v ps;
    opt v.expr c;
    decl v d
  | Namespace (_, ds) -> each (decl v) ds
  | Function f ->
    let entry (_, ts) = each v.type_ ts in
    entry f.path.outer;
    each entry f.path.inner;
    v.type_ f.return_type;
    ( match f.shape with
    | Definition (ps, body) ->
      fields v ps;
      each v.stmt body
    | Declaration ps -> fields v ps )
  | Struct s | Merged_struct_members s -> struct_ v s
  | Variable x ->
    v.type_ x.type_;
    v.expr x.init
  | Concept (_, e) | Static_assert (e, _) -> v.expr e
  | Type_alias a ->
    template_parameters v a.type_params;
    opt v.type_ a.rhs
  | Struct_forward_declaration (ps, _) | Enum {type_params = ps; _} -> template_parameters v ps
  | Member_definition m ->
    template_parameters v m.type_params;
    out_of_line v m.member

(** The types a type holds directly: an application's type arguments (not
    its value arguments), a mapping's type arguments, a type constructor's
    head.  A [decltype]'s expression is not a type's child. *)
let type_children : type p. (p Type.t -> unit) -> p Type.t -> unit =
 fun f t ->
  match t with
  | Entity_application (_, ts, _) | Named (_, ts) | External (_, ts) | Variant (_, ts) -> each f ts
  | Foreign fr -> each f fr.types
  | Function (dom, cod) ->
    each f dom;
    f cod
  | Const t | Shared_pointer t | Reference (_, t) | Pointer t | In_namespace (_, t) | Member (t, _) | Decay t
  | Non_deduced t | Type_constructor t ->
    f t
  | Apply (h, ts) ->
    f h;
    each f ts
  | Rebind (h, x) ->
    f h;
    f x
  | Variable _ | Instance _ | Promoted_member _ | Erased _ | Void | Any | Carrier_parameter | Auto | Type_of _
  | Decltype_auto | Obligation _ ->
    ()

(** Whether [p] holds of [t] or of a type inside it ({!type_children}): a
    type constructor's head is entered, a [decltype]'s expression is not. *)
let rec exists_type : type p. (p Type.t -> bool) -> p Type.t -> bool =
 fun p t ->
  p t
  ||
  let found = ref false in
  type_children (fun t -> if not !found then found := exists_type p t) t;
  !found
