(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Target language for extraction: a core C++ called MiniCpp.

    Crane's extraction pipeline has two intermediate representations:

    Rocq CIC --[extraction.ml]--> MiniML --[translation.ml]--> MiniCpp
    --[cpp.ml]--> C++

    MiniML and MiniCpp serve different purposes and cannot be merged:

    MiniML (defined in miniml.ml) is the result of extracting Rocq's Calculus of
    Inductive Constructions into a simply-typed functional language. This step
    performs type erasure (removing propositions, universe levels, implicit
    arguments), computes signatures that track which arguments survive
    extraction (Keep/Kill), and produces a clean ML-like AST with ~15
    constructors. MiniML enables 1,700 lines of optimizations in mlutil.ml
    (beta-iota reduction, dead code elimination, inlining, match simplification)
    that operate on type-erased terms — much simpler than working on raw CIC
    terms with their 30+ constructors and dependent types. MiniML also provides
    type reconstruction infrastructure (Tmeta with mutable unification) and
    buffers Crane from changes to Rocq's internal term representation across
    versions.

    MiniCpp (defined here) is a C++-oriented AST that translation.ml produces
    from MiniML. Where MiniML is language-agnostic (it could target OCaml,
    Haskell, or Scheme), MiniCpp captures C++-specific concepts:
    shared_ptr/unique_ptr memory management, std::variant for inductives,
    templates, concepts, namespaces, structs with visibility, move semantics,
    const/static/extern modifiers, constructors, methods, enum classes, and raw
    C++ escape hatches. The MiniML-to-MiniCpp translation resolves how each
    functional programming pattern maps to C++ idioms (e.g. MLcase becomes
    std::visit with an overloaded visitor, MLcons becomes a factory function
    returning shared_ptr, modules become structs, module types become concepts).

    Attempting to go directly from Rocq CIC to MiniCpp would require combining
    type erasure, optimization, and C++ idiom selection into a single pass —
    losing the optimization opportunities that MiniML provides and coupling Rocq
    internals directly to C++ generation. *)

open Names

(** {2 Pre-resolved C++ name}
    Computed during translation so the pretty-printer doesn't need
    name-resolution logic. *)

(** Pre-resolved C++ name, computed during translation. *)
type cpp_name = {
  cn_base : string; (* e.g., "add", "list", "Nat" *)
  cn_qualified : string option; (* Some "Nat::" for wrapper-qualified names *)
  cn_needs_typename : bool; (* true if dependent type in template context *)
}

(** {2 Inductive classification}

    Determined once during translation. *)

(** Classification of an inductive type for C++ code generation. *)
type cpp_ind_kind =
  | IK_Standard (* std::variant sum type *)
  | IK_Enum (* enum class *)
  | IK_Record of GlobRef.t option list (* struct with named fields *)
  | IK_Eponymous of GlobRef.t option list (* record merged into module *)
  | IK_TypeClass of GlobRef.t option list (* C++ concept *)

(** Custom extraction info, resolved once during translation. *)
type custom_info = {
  ci_inline : string option; (* Some code if to_inline, None otherwise *)
  ci_is_custom : bool;
}

(** Visibility for struct members. *)
type cpp_visibility =
  | VPublic
  | VPrivate

(** BDE section tags for struct member grouping. *)
type section_tag =
  | STypes
  | SData
  | SCreators
  | SManipulators
  | SAccessors
  | SNoTag

(** {2 C++ type expressions} *)

(** C++ type modifiers. *)
type cpp_tymod =
  | TMconst
  | TMstatic
  | TMextern

type cpp_type =
  | Tvar of int * Id.t option
  | Tid of Id.t * cpp_type list
    (* Simple Id-based type, for local names like nested structs *)
  | Tid_external of Id.t * cpp_type list
    (* External type from a header — never struct-qualified *)
  | Tglob of GlobRef.t * cpp_type list * cpp_expr list
  | Tfun of cpp_type list * cpp_type
  | Tmod of cpp_tymod * cpp_type
  | Tnamespace of GlobRef.t * cpp_type
  | Tqualified of
      cpp_type * Id.t (* typename Base<T>::nested - for nested struct access *)
  | Tref of cpp_type
  | Tptr of cpp_type
  | Tvariant of cpp_type list
  | Tshared_ptr of cpp_type
  | Tunique_ptr of cpp_type
  | Tvoid
  | Ttodo
  | Tunknown
  | Tany (* std::any - for type-erased storage of existential types *)
  | Tauto (* auto - for phantom tvar positions where C++ cannot deduce the type *)
  | Tdecltype of cpp_expr (* decltype(expr) *)

(** C++ type meta-variable for unification. *)
and cpp_meta = {
  id : int;
  mutable contents : cpp_type option;
}

(** C++ statements. *)
and cpp_stmt =
  | Sreturn of cpp_expr option
  | Sdecl of Id.t * cpp_type
  | Sasgn of Id.t * cpp_type option * cpp_expr
  | Sexpr of cpp_expr
  | Scustom_case of
      cpp_type
      * cpp_expr
      * cpp_type list
      * ((Id.t * cpp_type) list * cpp_type * cpp_stmt list) list
      * string
  | Sthrow of string (* throw statement for unreachable/absurd cases *)
  | Sswitch of cpp_expr * GlobRef.t * (Id.t * cpp_stmt list) list * cpp_stmt list option
    (* switch on enum: scrutinee, enum type, branches, optional default body *)
  | Sassert of string * string option
    (* runtime assert: C++ expression string, optional Rocq predicate comment *)
  | Sif of cpp_expr * cpp_stmt list * cpp_stmt list
    (* if-else: condition, then-branch, else-branch. Used for reuse
       optimization's use_count() check. *)
  | Sraw of string
    (* Raw C++ code, printed verbatim. Used for low-level operations in reuse
       optimization. *)
  | Sstruct_def of Id.t * (Id.t * cpp_type) list
    (* Local struct definition: struct Name { T1 f1; T2 f2; }; *)
  | Susing of Id.t * cpp_type
    (* Local using alias: using Name = Type; *)
  | Sdecl_init of Id.t * cpp_type
    (* Value-initialized declaration: Type name{}; *)
  | Sassign_field of cpp_expr * Id.t * cpp_expr
  (* Field assignment: obj.field = expr. Used for in-place mutation during
     memory reuse. *)
  | Sderef_asgn of Id.t * cpp_expr
  (* Dereference assignment: [*id = expr;].  Introduced for the
     [shared_ptr<std::function>] fixpoint pattern where a fixpoint is
     allocated as [auto f = make_shared<function<...>>()] and the body is
     assigned via [*f = [=](...) mutable { ... }].  The indirection allows
     the by-value lambda to capture [f] (a [shared_ptr] copy) instead of a
     dangling [&]-reference.  See {!Translation.gen_local_fix_shared_ptr}. *)
  | Swhile of cpp_expr * cpp_stmt list
    (* while (condition) { body } — used by loopify pass *)
  | Sblock of cpp_stmt list
    (* { stmts } — scoped block for local declarations *)
  | Scontinue
    (* continue; — used in loopified while loops *)
  | Sbreak
    (* break; — used in loopified while loops *)
  | Sblock_custom of
      GlobRef.t
      * string (* template string containing %result *)
      * Id.t (* result variable name *)
      * cpp_type (* result variable type *)
      * cpp_expr list (* value args for %a0, %a1, ... *)
      * cpp_type list (* type args for %t0, %t1, ... *)
    (* Block template expansion: multi-statement inline custom that
       substitutes %result with the bind target variable name. *)
  | Smatch of smatch_branch list * cpp_stmt list option
    (* If/else-if pattern match chain using std::holds_alternative and std::get.
       Branches are checked in order. The optional else body is [Some stmts] for
       a wildcard/default case, or [None] to emit std::unreachable(). *)

(** A branch in an [Smatch] if/else-if pattern match chain. *)
and smatch_branch = {
  smb_scrutinee : cpp_expr;
    (** Variant accessor expression, e.g. [scrut->v()] or [scrut.v()].
        Each branch carries its own scrutinee so that multi-match branches
        can reference different scrutinees. *)
  smb_ctor_type : cpp_type;
    (** Constructor struct type for the [std::holds_alternative] /
        [std::get] template argument. *)
  smb_var : Id.t option;
    (** Binding variable for [std::get], or [None] when no fields
        are accessed in the branch body.  Kept for scrutinee-name
        derivation even when {!smb_field_bindings} is non-empty. *)
  smb_field_bindings : (Id.t * cpp_type * bool) list;
    (** Ordered list of [(binding_name, field_cpp_type, used)] for C++
        structured bindings ([const auto& [f1, f2] = std::get<T>(…)]).
        Covers ALL constructor fields in struct-declaration order.
        [used] is [true] when the binding is referenced in the branch
        body; unused bindings are annotated [[[maybe_unused]]].
        Empty when no fields are used or for frame-dispatch branches. *)
  smb_extra_conds : cpp_expr list;
    (** Additional [&&]-joined conditions after the primary check. *)
  smb_reuse : (cpp_expr * Id.t option * cpp_stmt list) option;
    (** When [Some (cond, rf_var, body)], the branch has a reuse fast-path:
        the printer emits [if (cond) { get_ref; body } else { bindings; normal }]
        inside the [holds_alternative] block.  When [rf_var = Some id], the
        printer emits [auto& id = std::get<smb_ctor_type>(scrut->v_mut())]
        before the body.  The condition is typically [use_count() == 1].
        [None] for branches without reuse. *)
  smb_is_value_type : bool;
    (** When [true], the scrutinee is a value type (not shared_ptr).
        Affects binding style: value types use [.v()] / [.v_mut()],
        pointer types use [->v()] / [->v_mut()]. *)
  smb_is_owned : bool;
    (** When [true], the scrutinee is owned (last use or explicit move).
        Affects binding: owned value types use [auto [...] = std::move(std::get<T>(scrut.v_mut()))],
        borrowed value types use [const auto& [...] = std::get<T>(scrut.v())]. *)
  smb_body : cpp_stmt list;
    (** Branch body statements.  When {!smb_field_bindings} is non-empty,
        field accesses use direct [CPPvar binding_name] references. *)
}

(** C++ expressions. *)
and cpp_expr =
  | CPPvar of Id.t
  | CPPglob of GlobRef.t * cpp_type list * custom_info option
  | CPPnamespace of GlobRef.t * cpp_expr
  | CPPfun_call of cpp_expr * cpp_expr list
  | CPPderef of cpp_expr
  | CPPmove of cpp_expr
  | CPPforward of cpp_type * cpp_expr
  | CPPlambda of
      (cpp_type * Id.t option) list
      * cpp_type option
      * cpp_stmt list
      * bool (* capture_by_value *)
  | CPPvisit
  | CPPmk_shared of cpp_type
  | CPPoverloaded of cpp_expr list
    (* cpp_expressions in list should only be lambdas. TODO: enforce in the AST?
       split up to a funcall *)
  | CPPstructmk of GlobRef.t * cpp_type list * cpp_expr list
  | CPPstruct of
      GlobRef.t
      * cpp_type list
      * cpp_expr list (* record struct construction via namespace *)
  | CPPstruct_id of
      Id.t
      * cpp_type list
      * cpp_expr list (* Local struct init with Id, e.g., Leaf{} *)
  | CPPget of cpp_expr * Id.t (* access from a struct (or class) *)
  | CPPget' of cpp_expr * GlobRef.t (* access from a struct (or class) *)
  | CPPstring of Pstring.t
  | CPPuint of Uint63.t
  | CPPfloat of Float64.t
  | CPPparray of cpp_expr array * cpp_expr
  | CPPrequires of
      (cpp_type * Id.t) list * (cpp_expr * cpp_constraint) list * cpp_type list
  (* requires (params) { typename type_reqs; { expr } -> constraint; } *)
  | CPPnew of cpp_type * cpp_expr list (* new Type(args) or new Type{args} *)
  | CPPshared_ptr_ctor of cpp_type * cpp_expr (* std::shared_ptr<T>(expr) *)
  | CPPunique_ptr_ctor of cpp_type * cpp_expr (* std::unique_ptr<T>(expr) *)
  | CPPmk_unique of cpp_type (* std::make_unique<T> *)
  | CPPthis (* this pointer in methods *)
  | CPPshared_from_this of cpp_type
    (* std::const_pointer_cast<T>(shared_from_this()) — for returning this as
       shared_ptr *)
  | CPPmember of cpp_expr * Id.t (* expr.member - for accessing v_ etc *)
  | CPParrow of cpp_expr * Id.t (* expr->member - for ptr->v_ access *)
  | CPPmethod_call of cpp_expr * Id.t * cpp_expr list (* obj->method(args) *)
  | CPPqualified of
      cpp_expr * Id.t (* expr::id - for qualified name access like Type::ctor *)
  | CPPconvertible_to of cpp_type (* std::convertible_to<T> constraint *)
  | CPPabort of string (* unreachable code / absurd case - calls std::abort() *)
  | CPPenum_val of
      GlobRef.t * Id.t (* enum class value: EnumType::Constructor *)
  | CPPraw of string
    (* Raw C++ expression, printed verbatim. Used for low-level operations
       (e.g., literal "1" for use_count check). *)
  | CPPbinop of string * cpp_expr * cpp_expr
    (* Binary operator: operator string, lhs, rhs. Used for conditions in reuse
       optimization (&&, ==). *)
  | CPPbool of bool (* true / false literal *)
  | CPPint of int (* integer literal *)
  | CPPbrace_init (* {} — empty brace initialization *)
  | CPPunop of string * cpp_expr (* unary operator: !expr, -expr, etc. *)
  | CPPany_cast of cpp_type * cpp_expr
    (* std::any_cast<T>(expr) — recovers a typed value from std::any *)

(** A C++ constraint expression (used in requires clauses). *)
and cpp_constraint = cpp_expr

(** Template parameter kinds. *)
and template_type =
  | TTtypename
  | TTtypename_default of cpp_type (* typename T = default_type *)
  | TTfun of (cpp_type list * cpp_type)
  | TTconcept of GlobRef.t (* e.g., 'Eq T' *)

(** Struct/class field declarations. *)
and cpp_field =
  | Fvar of Id.t * cpp_type
  | Fvar' of GlobRef.t * cpp_type
  | Ffundef of Id.t * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
  | Ffundecl of Id.t * cpp_type * (Id.t * cpp_type) list
  | Fmethod of method_field
  (* Private constructor: params, initializer list (as stmts for v_(x) style) *)
  | Fconstructor of
      (Id.t * cpp_type) list
      * (Id.t * cpp_expr) list
      * bool (* bool = explicit *)
  (* Nested struct with its own visibility-annotated fields *)
  | Fnested_struct of Id.t * (cpp_field * cpp_visibility * section_tag) list
  (* Nested using declaration *)
  | Fnested_using of Id.t * cpp_type
  (* Deleted default constructor: ctor() = delete *)
  | Fdeleted_ctor

(** Method field descriptor for struct methods. *)
and method_field = {
  mf_name : Id.t;
  mf_tparams : (template_type * Id.t) list;
  mf_ret_type : cpp_type;
  mf_params : (Id.t * cpp_type) list;
  mf_body : cpp_stmt list;
  mf_is_const : bool;
  mf_is_static : bool;
  mf_this_pos : int;
  mf_no_pure : bool;
}

(** C++ type schema. The integer is the number of variables in the schema. *)
type cpp_schema = int * cpp_type

(** Construct a shared_ptr type wrapping an inductive type (for recursive
    self-references in constructor fields). Using shared_ptr keeps the value type
    copyable; unique_ptr would require clone() generation. *)
let ind_ty_ptr id vars = Tshared_ptr (Tglob (id, vars, []))

(** Rvalue reference type [T&&].  Uses the double-{!Tref} encoding that the
    pretty-printer already handles: [Tref(Tref(t))] prints as [t&&]. *)
let rval_ref ty = Tref (Tref ty)

(** {2 Generic AST traversal combinators}

    These enable writing AST transformations without manually matching every
    constructor. Pass custom cases for the constructors you care about; the
    combinator handles structural recursion for the rest. *)

(** [map_cpp_type f ty] applies [f] to every sub-type in [ty]. Use this to build
    type transformations: pass a function that handles your custom case and
    delegates to [map_cpp_type f] for the recursive case. *)
let rec map_cpp_type (f : cpp_type -> cpp_type) (ty : cpp_type) : cpp_type =
  let ty = f ty in
  match ty with
  | Tglob (r, tys, args) -> Tglob (r, List.map (map_cpp_type f) tys, args)
  | Tid (id, tys) -> Tid (id, List.map (map_cpp_type f) tys)
  | Tid_external (id, tys) -> Tid_external (id, List.map (map_cpp_type f) tys)
  | Tfun (dom, cod) -> Tfun (List.map (map_cpp_type f) dom, map_cpp_type f cod)
  | Tmod (m, t) -> Tmod (m, map_cpp_type f t)
  | Tshared_ptr t -> Tshared_ptr (map_cpp_type f t)
  | Tunique_ptr t -> Tunique_ptr (map_cpp_type f t)
  | Tref t -> Tref (map_cpp_type f t)
  | Tptr t -> Tptr (map_cpp_type f t)
  | Tvariant ts -> Tvariant (List.map (map_cpp_type f) ts)
  | Tnamespace (r, t) -> Tnamespace (r, map_cpp_type f t)
  | Tqualified (t, id) -> Tqualified (map_cpp_type f t, id)
  | Tdecltype _ -> ty (* decltype wraps CPPraw, no sub-types to map *)
  | Tvar _ | Tvoid | Ttodo | Tunknown | Tany | Tauto -> ty

(** [map_expr fe fs ft e] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent. *)
let map_expr
    (fe : cpp_expr -> cpp_expr)
    (fs : cpp_stmt -> cpp_stmt)
    (ft : cpp_type -> cpp_type)
    (e : cpp_expr) : cpp_expr =
  match e with
  | CPPvar _ -> e
  | CPPglob (r, tys, ci) -> CPPglob (r, List.map ft tys, ci)
  | CPPnamespace (r, e') -> CPPnamespace (r, fe e')
  | CPPfun_call (f, args) -> CPPfun_call (fe f, List.map fe args)
  | CPPderef e' -> CPPderef (fe e')
  | CPPmove e' -> CPPmove (fe e')
  | CPPforward (ty, e') -> CPPforward (ft ty, fe e')
  | CPPlambda (params, ret_ty, stmts, capture) ->
    CPPlambda
      ( List.map (fun (ty, id) -> (ft ty, id)) params,
        Option.map ft ret_ty,
        List.map fs stmts,
        capture )
  | CPPvisit -> e
  | CPPmk_shared ty -> CPPmk_shared (ft ty)
  | CPPoverloaded exprs -> CPPoverloaded (List.map fe exprs)
  | CPPstructmk (r, tys, args) ->
    CPPstructmk (r, List.map ft tys, List.map fe args)
  | CPPstruct (r, tys, args) -> CPPstruct (r, List.map ft tys, List.map fe args)
  | CPPstruct_id (id, tys, args) ->
    CPPstruct_id (id, List.map ft tys, List.map fe args)
  | CPPget (e', id) -> CPPget (fe e', id)
  | CPPget' (e', r) -> CPPget' (fe e', r)
  | CPPstring _ | CPPuint _ | CPPfloat _ -> e
  | CPPparray (arr, def) -> CPPparray (Array.map fe arr, fe def)
  | CPPrequires (params, constrs, tyreqs) ->
    CPPrequires
      ( List.map (fun (ty, id) -> (ft ty, id)) params,
        List.map (fun (e', c) -> (fe e', fe c)) constrs,
        List.map ft tyreqs )
  | CPPnew (ty, args) -> CPPnew (ft ty, List.map fe args)
  | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ft ty, fe e')
  | CPPunique_ptr_ctor (ty, e') -> CPPunique_ptr_ctor (ft ty, fe e')
  | CPPmk_unique ty -> CPPmk_unique (ft ty)
  | CPPthis -> e
  | CPPshared_from_this ty -> CPPshared_from_this (ft ty)
  | CPPmember (e', id) -> CPPmember (fe e', id)
  | CPParrow (e', id) -> CPParrow (fe e', id)
  | CPPmethod_call (obj, id, args) ->
    CPPmethod_call (fe obj, id, List.map fe args)
  | CPPqualified (e', id) -> CPPqualified (fe e', id)
  | CPPconvertible_to ty -> CPPconvertible_to (ft ty)
  | CPPabort _ -> e
  | CPPenum_val _ -> e
  | CPPraw _ -> e
  | CPPbinop (op, e1, e2) -> CPPbinop (op, fe e1, fe e2)
  | CPPbool _ -> e
  | CPPint _ -> e
  | CPPbrace_init -> e
  | CPPunop (op, e') -> CPPunop (op, fe e')
  | CPPany_cast (ty, e') -> CPPany_cast (ft ty, fe e')

(** [map_stmt fe fs ft s] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent. *)
let map_stmt
    (fe : cpp_expr -> cpp_expr)
    (fs : cpp_stmt -> cpp_stmt)
    (ft : cpp_type -> cpp_type)
    (s : cpp_stmt) : cpp_stmt =
  match s with
  | Sreturn None -> s
  | Sreturn (Some e) -> Sreturn (Some (fe e))
  | Sdecl (id, ty) -> Sdecl (id, ft ty)
  | Sasgn (id, ty_opt, e) -> Sasgn (id, Option.map ft ty_opt, fe e)
  | Sexpr e -> Sexpr (fe e)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    Scustom_case
      ( ft ty,
        fe scrut,
        List.map ft tyargs,
        List.map
          (fun (params, ret_ty, body) ->
            ( List.map (fun (id, ty) -> (id, ft ty)) params,
              ft ret_ty,
              List.map fs body ) )
          branches,
        err )
  | Sthrow _ -> s
  | Sswitch (scrut, r, branches, default) ->
    Sswitch
      (fe scrut, r, List.map (fun (id, body) -> (id, List.map fs body)) branches,
       Option.map (List.map fs) default)
  | Sassert _ -> s
  | Sif (cond, then_br, else_br) ->
    Sif (fe cond, List.map fs then_br, List.map fs else_br)
  | Sraw _ -> s
  | Sstruct_def (id, fields) ->
    Sstruct_def (id, List.map (fun (fid, ty) -> (fid, ft ty)) fields)
  | Susing (id, ty) -> Susing (id, ft ty)
  | Sdecl_init (id, ty) -> Sdecl_init (id, ft ty)
  | Sassign_field (obj, field, e) -> Sassign_field (fe obj, field, fe e)
  | Sderef_asgn (id, e) -> Sderef_asgn (id, fe e)
  | Swhile (cond, body) -> Swhile (fe cond, List.map fs body)
  | Sblock stmts -> Sblock (List.map fs stmts)
  | Scontinue -> s
  | Sbreak -> s
  | Sblock_custom (r, tmpl, id, ty, args, tys) ->
    Sblock_custom (r, tmpl, id, ft ty, List.map fe args, List.map ft tys)
  | Smatch (branches, default) ->
    Smatch
      ( List.map
          (fun br ->
            { smb_scrutinee = fe br.smb_scrutinee;
              smb_ctor_type = ft br.smb_ctor_type;
              smb_var = br.smb_var;
              smb_field_bindings =
                List.map (fun (id, ty, u) -> (id, ft ty, u)) br.smb_field_bindings;
              smb_extra_conds = List.map fe br.smb_extra_conds;
              smb_reuse =
                Option.map (fun (cond, rf, stmts) ->
                  (fe cond, rf, List.map fs stmts)) br.smb_reuse;
              smb_is_value_type = br.smb_is_value_type;
              smb_is_owned = br.smb_is_owned;
              smb_body = List.map fs br.smb_body })
          branches,
        Option.map (List.map fs) default )

(** Iterate over the immediate children of a [cpp_expr], calling [on_expr]
    for child expressions and [on_stmts] for child statement lists.  Does
    not recurse — the caller controls recursion depth.  Covers every
    constructor in {!cpp_expr}. *)
let iter_expr_children ~on_expr ~on_stmts (e : cpp_expr) : unit =
  match e with
  | CPPvar _ | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPmk_unique _
  | CPPstring _ | CPPuint _ | CPPfloat _ | CPPconvertible_to _
  | CPPabort _ | CPPenum_val _ | CPPraw _ | CPPbool _ | CPPint _
  | CPPbrace_init | CPPthis | CPPshared_from_this _ -> ()
  | CPPfun_call (f, args) -> on_expr f; List.iter on_expr args
  | CPPnamespace (_, e') | CPPderef e' | CPPmove e' | CPPforward (_, e')
  | CPPget (e', _) | CPPget' (e', _) | CPPmember (e', _) | CPParrow (e', _)
  | CPPqualified (e', _) | CPPshared_ptr_ctor (_, e')
  | CPPunique_ptr_ctor (_, e') | CPPany_cast (_, e') | CPPunop (_, e') ->
    on_expr e'
  | CPPlambda (_, _, stmts, _) -> on_stmts stmts
  | CPPoverloaded es | CPPstructmk (_, _, es) | CPPstruct (_, _, es)
  | CPPstruct_id (_, _, es) | CPPnew (_, es) ->
    List.iter on_expr es
  | CPPparray (arr, e') -> Array.iter on_expr arr; on_expr e'
  | CPPmethod_call (obj, _, args) -> on_expr obj; List.iter on_expr args
  | CPPrequires (_, constraints, _) ->
    List.iter (fun (e', _) -> on_expr e') constraints
  | CPPbinop (_, l, r) -> on_expr l; on_expr r

(** Iterate over the immediate children of a [cpp_stmt], calling [on_expr]
    for child expressions and [on_stmts] for child statement lists.  Does
    not recurse — the caller controls recursion depth.  Covers every
    constructor in {!cpp_stmt}. *)
let iter_stmt_children ~on_expr ~on_stmts (s : cpp_stmt) : unit =
  match s with
  | Sreturn (Some e) | Sexpr e -> on_expr e
  | Sreturn None | Sdecl _ | Sthrow _ | Sassert _ | Sraw _
  | Sstruct_def _ | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> ()
  | Sasgn (_, _, e) -> on_expr e
  | Sif (cond, then_br, else_br) ->
    on_expr cond; on_stmts then_br; on_stmts else_br
  | Sswitch (scrut, _, branches, default) ->
    on_expr scrut;
    List.iter (fun (_, stmts) -> on_stmts stmts) branches;
    Option.iter on_stmts default
  | Scustom_case (_, scrut, _, branches, _) ->
    on_expr scrut;
    List.iter (fun (_, _, stmts) -> on_stmts stmts) branches
  | Sassign_field (obj, _, e) -> on_expr obj; on_expr e
  | Sderef_asgn (_, e) -> on_expr e
  | Swhile (cond, body) -> on_expr cond; on_stmts body
  | Sblock stmts -> on_stmts stmts
  | Sblock_custom (_, _, _, _, args, _) -> List.iter on_expr args
  | Smatch (branches, default) ->
    List.iter (fun br ->
      on_expr br.smb_scrutinee;
      List.iter on_expr br.smb_extra_conds;
      ( match br.smb_reuse with
      | Some (cond, _, stmts) -> on_expr cond; on_stmts stmts
      | None -> () );
      on_stmts br.smb_body) branches;
    Option.iter on_stmts default

(** C++ top-level declarations. *)
type cpp_decl =
  | Dtemplate of (template_type * Id.t) list * cpp_constraint option * cpp_decl
  | Dnspace of GlobRef.t option * cpp_decl list
  | Dfundef of
      (GlobRef.t * cpp_type list) list
      * cpp_type
      * (Id.t * cpp_type) list
      * cpp_stmt list
      * bool (* no_pure: suppress __attribute__((pure)) for monadic functions *)
  | Dfundecl of
      (GlobRef.t * cpp_type list) list
      * cpp_type
      * (Id.t option * cpp_type) list
      * bool (* suppress __attribute__((pure)) — e.g. axiom stubs that throw *)
  | Dstruct of {
      ds_ref : GlobRef.t;
      ds_fields : (cpp_field * cpp_visibility * section_tag) list;
      ds_tparams : (template_type * Id.t) list;
          (* [] for non-template structs *)
      ds_constraint : cpp_constraint option; (* template constraint, if any *)
      ds_needs_shared_from_this : bool;
          (* inherit enable_shared_from_this when a method returns this *)
    }
  | Dstruct_decl of GlobRef.t
  | Dusing of GlobRef.t * cpp_type
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
  | Ddecl of GlobRef.t * cpp_type
  | Dconcept of
      GlobRef.t
      * cpp_expr (* template params are provided by an outer Dtemplate *)
  | Dstatic_assert of cpp_expr * string option
  | Denum of {
      de_ref : GlobRef.t;
      de_ctors : Id.t list;
      de_ctor_rocq_names : string list;
      de_tparams : (template_type * Id.t) list;
    }
