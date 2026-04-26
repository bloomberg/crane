(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Target language for extraction: a core C++ called MiniCpp.

   Crane's extraction pipeline has two intermediate representations:

   Rocq CIC --[extraction.ml]--> MiniML --[translation.ml]--> MiniCpp
   --[cpp.ml]--> C++

   MiniML (miniml.ml) handles type erasure, signature computation, and ML-level
   optimizations on a language-agnostic functional AST. MiniCpp (this file)
   captures C++-specific idioms: shared_ptr/unique_ptr memory management,
   std::variant, templates, concepts, namespaces, structs with visibility, move
   semantics, enum classes, and constructors.

   See minicpp.ml for a detailed explanation of why both representations are
   needed and cannot be merged. *)

open Names

(** {2 Pre-resolved C++ name}

    Computed during translation so the pretty-printer doesn't need
    name-resolution logic. *)

(** Pre-resolved C++ identifier with qualification information. *)
type cpp_name = {
  cn_base : string;  (** Base identifier, e.g., "add", "list", "Nat" *)
  cn_qualified : string option;
      (** Optional qualifier prefix, e.g., Some "Nat::" *)
  cn_needs_typename : bool;
      (** True if dependent type requires typename keyword in template context
      *)
}

(** {2 Inductive classification}

    Determined once during translation. *)

(** Classification of an inductive type for C++ code generation. *)
type cpp_ind_kind =
  | IK_Standard  (** Sum type rendered as std::variant *)
  | IK_Enum  (** Simple enumeration rendered as enum class *)
  | IK_Record of GlobRef.t option list
      (** Product type rendered as struct, with field references *)
  | IK_Eponymous of GlobRef.t option list
      (** Record merged into its module struct to avoid naming conflicts *)
  | IK_TypeClass of GlobRef.t option list
      (** Type class rendered as C++ concept *)

(** {2 Custom extraction info}

    Resolved once during translation. *)

(** Custom extraction metadata for manually mapped entities. *)
type custom_info = {
  ci_inline : string option;
      (** Some code if entity should be inlined, None otherwise *)
  ci_is_custom : bool;  (** True if entity has custom C++ mapping *)
}

(** {2 Visibility modifiers} *)

(** Visibility for struct members (C++ public/private). *)
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

(** {2 C++ type modifiers} *)

(** Type modifiers (const, static, extern). *)
type cpp_tymod =
  | TMconst  (** Const qualifier *)
  | TMstatic  (** Static storage class *)
  | TMextern  (** External linkage *)

(** {2 C++ type expressions} *)

(** C++ type representation. *)
type cpp_type =
  | Tvar of int * Id.t option
      (** Type variable with De Bruijn index and optional name *)
  | Tid of Id.t * cpp_type list
      (** Local type identifier with type arguments, for nested structs *)
  | Tid_external of Id.t * cpp_type list
      (** External type from a header — never struct-qualified *)
  | Tglob of GlobRef.t * cpp_type list * cpp_expr list
      (** Global type reference with type and value arguments *)
  | Tfun of cpp_type list * cpp_type
      (** Function type: domain types and codomain *)
  | Tmod of cpp_tymod * cpp_type
      (** Type with modifier (const, static, extern) *)
  | Tnamespace of GlobRef.t * cpp_type
      (** Type qualified by namespace reference *)
  | Tqualified of cpp_type * Id.t
      (** Nested type access, e.g., typename Base<T>::nested *)
  | Tref of cpp_type  (** C++ reference type *)
  | Tptr of cpp_type  (** C++ pointer type *)
  | Tvariant of cpp_type list  (** std::variant<...> for sum types *)
  | Tshared_ptr of cpp_type  (** std::shared_ptr<T> for managed memory *)
  | Tunique_ptr of cpp_type  (** std::unique_ptr<T> for unique ownership *)
  | Tvoid  (** void type *)
  | Ttodo  (** Placeholder during development *)
  | Tunknown  (** Type inference failed *)
  | Tany  (** std::any for type-erased storage of existentials *)
  | Tauto
      (** auto for phantom tvar positions where C++ cannot deduce the type *)
  | Tdecltype of cpp_expr  (** decltype(expr) for deduced types *)

(** Type metavariable for unification. *)
and cpp_meta = {
  id : int;  (** Unique identifier *)
  mutable contents : cpp_type option;
      (** Unification result, None if unresolved *)
}

(** {2 C++ statements} *)

(** C++ statement representation. *)
and cpp_stmt =
  | Sreturn of cpp_expr option  (** Return statement with optional expression *)
  | Sdecl of Id.t * cpp_type  (** Variable declaration *)
  | Sasgn of Id.t * cpp_type option * cpp_expr
      (** Variable assignment with optional type annotation *)
  | Sexpr of cpp_expr  (** Expression statement *)
  | Scustom_case of
      cpp_type
      * cpp_expr
      * cpp_type list
      * ((Id.t * cpp_type) list * cpp_type * cpp_stmt list) list
      * string
      (** Custom pattern match: return type, scrutinee, type args, branches
          (params, type, body), custom match string *)
  | Sthrow of string
      (** Throw exception with message, for unreachable/absurd cases *)
  | Sswitch of cpp_expr * GlobRef.t * (Id.t * cpp_stmt list) list * cpp_stmt list option
      (** Switch statement: scrutinee, enum type reference, branches
          (constructor, body), optional default body (None = std::unreachable) *)
  | Sassert of string * string option
      (** Runtime assertion: C++ condition, optional Rocq predicate comment *)
  | Sif of cpp_expr * cpp_stmt list * cpp_stmt list
      (** Conditional: condition, then-branch, else-branch (used for reuse
          optimization) *)
  | Sraw of string  (** Raw C++ code printed verbatim *)
  | Sstruct_def of Id.t * (Id.t * cpp_type) list
      (** Local struct definition: struct Name { T1 f1; T2 f2; }; *)
  | Susing of Id.t * cpp_type
      (** Local using alias: using Name = Type; *)
  | Sdecl_init of Id.t * cpp_type
      (** Value-initialized declaration: Type name{}; *)
  | Sassign_field of cpp_expr * Id.t * cpp_expr
      (** Field assignment for in-place mutation during memory reuse *)
  | Sderef_asgn of Id.t * cpp_expr
      (** Dereference assignment: [*id = expr].  Used by the
          [shared_ptr<std::function>] fixpoint pattern to assign through
          the pointer indirection.
          See {!Translation.gen_local_fix_shared_ptr}. *)
  | Swhile of cpp_expr * cpp_stmt list
      (** While loop: condition and body (used by loopify pass) *)
  | Sblock of cpp_stmt list  (** Scoped block for local declarations *)
  | Scontinue  (** Continue statement for loopified while loops *)
  | Sbreak  (** Break statement for loopified while loops *)
  | Sblock_custom of
      GlobRef.t
      * string
      * Id.t
      * cpp_type
      * cpp_expr list
      * cpp_type list
      (** Block template expansion: multi-statement inline custom that
          substitutes [%result] with the bind target variable name. *)
  | Smatch of smatch_branch list * cpp_stmt list option
      (** If/else-if pattern match chain using [std::holds_alternative] and
          [std::get].  Branches are checked in order.  The optional else
          body is [Some stmts] for a wildcard/default case, or [None] to
          emit [std::unreachable()]. *)

(** A branch in an {!Smatch} if/else-if pattern match chain.

    Each branch stores its own scrutinee expression because type refinement
    may yield different scrutinee expressions per branch (e.g., after
    inlining or CSE).  The printer extracts the common scrutinee from the
    first branch for the shared [auto&&] binding. *)
and smatch_branch = {
  smb_scrutinee : cpp_expr;
      (** Variant accessor expression, e.g. [scrut->v()] or [scrut.v()].
          Stored per-branch intentionally: branches may have different
          scrutinee expressions after type refinement; the printer extracts
          the common scrutinee from the first branch. *)
  smb_ctor_type : cpp_type;
      (** Constructor struct type for the template argument of
          [std::holds_alternative<T>] / [std::get<T>]. *)
  smb_var : Id.t option;
      (** Binding variable for [std::get], or [None] when the
          branch body doesn't use fields.  Kept for scrutinee-name
          derivation even when {!smb_field_bindings} is non-empty. *)
  smb_field_bindings : (Id.t * cpp_type * bool) list;
      (** Ordered list of [(binding_name, field_cpp_type, used)] for C++
          structured bindings ([const auto& [f1, f2] = std::get<T>(…)]).
          Covers ALL constructor fields in struct-declaration order.
          The [used] flag is [true] when the binding is referenced in the
          branch body; unused bindings are annotated [[[maybe_unused]]].
          Empty when no fields are used or for frame-dispatch branches. *)
  smb_extra_conds : cpp_expr list;
      (** Additional [&&]-joined conditions. *)
  smb_reuse : (cpp_expr * Id.t option * cpp_stmt list) option;
      (** When [Some (cond, rf_var, body)], the branch has a reuse fast-path.
          When [rf_var = Some id], the printer emits
          [auto& id = std::get<smb_ctor_type>(scrut->v_mut())] before the body.
          Typically [cond = use_count() == 1].  [None] for branches without
          reuse. *)
  smb_is_value_type : bool;
      (** When [true], the scrutinee is a value type (not shared_ptr). *)
  smb_is_owned : bool;
      (** When [true], the scrutinee is owned.  Owned value types use
          [auto [...] = std::move(std::get<T>(scrut.v_mut()))]. *)
  smb_body : cpp_stmt list;
      (** Branch body statements. *)
}

(** {2 C++ expressions} *)

(** C++ expression representation. *)
and cpp_expr =
  | CPPvar of Id.t  (** Local variable reference *)
  | CPPglob of GlobRef.t * cpp_type list * custom_info option
      (** Global reference with type arguments and optional custom extraction
          info *)
  | CPPnamespace of GlobRef.t * cpp_expr  (** Namespace-qualified expression *)
  | CPPfun_call of cpp_expr * cpp_expr list
      (** Function call with arguments (stored in reverse order) *)
  | CPPderef of cpp_expr  (** Pointer dereference *)
  | CPPmove of cpp_expr  (** std::move for move semantics *)
  | CPPforward of cpp_type * cpp_expr
      (** std::forward<T> for perfect forwarding *)
  | CPPlambda of
      (cpp_type * Id.t option) list * cpp_type option * cpp_stmt list * bool
      (** Lambda: params, optional return type, body, capture_by_value flag *)
  | CPPvisit  (** std::visit for variant pattern matching *)
  | CPPmk_shared of cpp_type  (** std::make_shared<T> factory function *)
  | CPPoverloaded of cpp_expr list
      (** Overloaded visitor set for variant matching *)
  | CPPstructmk of GlobRef.t * cpp_type list * cpp_expr list
      (** Struct construction via factory function *)
  | CPPstruct of GlobRef.t * cpp_type list * cpp_expr list
      (** Record struct construction via namespace-qualified initializer *)
  | CPPstruct_id of Id.t * cpp_type list * cpp_expr list
      (** Local struct initialization by Id, e.g., Leaf{args} *)
  | CPPget of cpp_expr * Id.t  (** Member access by local identifier *)
  | CPPget' of cpp_expr * GlobRef.t  (** Member access by global reference *)
  | CPPstring of Pstring.t  (** String literal *)
  | CPPuint of Uint63.t  (** Unsigned 63-bit integer literal *)
  | CPPfloat of Float64.t  (** Floating-point literal *)
  | CPPparray of cpp_expr array * cpp_expr
      (** Persistent array with element array and default value *)
  | CPPrequires of
      (cpp_type * Id.t) list * (cpp_expr * cpp_constraint) list * cpp_type list
      (** Requires expression: parameters, expression-constraint pairs, type
          requirements *)
  | CPPnew of cpp_type * cpp_expr list  (** Heap allocation: new Type(args) *)
  | CPPshared_ptr_ctor of cpp_type * cpp_expr
      (** Direct std::shared_ptr<T>(expr) construction *)
  | CPPunique_ptr_ctor of cpp_type * cpp_expr
      (** Direct std::unique_ptr<T>(expr) construction *)
  | CPPmk_unique of cpp_type  (** std::make_unique<T> factory function *)
  | CPPthis  (** this pointer in method context *)
  | CPPshared_from_this of cpp_type
      (** std::const_pointer_cast<T>(shared_from_this()) *)
  | CPPmember of cpp_expr * Id.t
      (** Member access with dot operator: expr.member *)
  | CPParrow of cpp_expr * Id.t
      (** Member access with arrow operator: expr->member *)
  | CPPmethod_call of cpp_expr * Id.t * cpp_expr list
      (** Method call: object, method name, arguments *)
  | CPPqualified of cpp_expr * Id.t  (** Scope resolution: expr::id *)
  | CPPconvertible_to of cpp_type  (** std::convertible_to<T> type trait *)
  | CPPabort of string  (** Unreachable code marker, calls std::abort() *)
  | CPPenum_val of GlobRef.t * Id.t
      (** Enum class value: EnumType::Constructor *)
  | CPPraw of string  (** Raw C++ expression code *)
  | CPPbinop of string * cpp_expr * cpp_expr
      (** Binary operator for reuse optimization conditions *)
  | CPPbool of bool  (** Boolean literal: true/false *)
  | CPPint of int  (** Integer literal *)
  | CPPbrace_init  (** Empty brace initialization: {} *)
  | CPPunop of string * cpp_expr  (** Unary operator: !expr, -expr, etc. *)
  | CPPany_cast of cpp_type * cpp_expr
      (** std::any_cast<T>(expr) — recovers typed value from std::any *)

(** Alias for constraint expressions in requires clauses. *)
and cpp_constraint = cpp_expr

(** {2 Template parameters} *)

(** Template parameter kinds. *)
and template_type =
  | TTtypename  (** Plain typename parameter *)
  | TTtypename_default of cpp_type
      (** typename with default: typename T = default_type *)
  | TTfun of (cpp_type list * cpp_type)
      (** Function type parameter for higher-order templates *)
  | TTconcept of GlobRef.t  (** Concept-constrained parameter, e.g., Eq T *)

(** {2 Struct fields} *)

(** Struct/class field declarations. *)
and cpp_field =
  | Fvar of Id.t * cpp_type  (** Field variable by local identifier *)
  | Fvar' of GlobRef.t * cpp_type  (** Field variable by global reference *)
  | Ffundef of Id.t * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
      (** Member function definition: name, return type, parameters, body *)
  | Ffundecl of Id.t * cpp_type * (Id.t * cpp_type) list
      (** Member function declaration without body *)
  | Fmethod of method_field  (** Method with full descriptor *)
  | Fconstructor of (Id.t * cpp_type) list * (Id.t * cpp_expr) list * bool
      (** Constructor: parameters, member initializer list, explicit flag *)
  | Fnested_struct of Id.t * (cpp_field * cpp_visibility * section_tag) list
      (** Nested struct definition with visibility-annotated fields *)
  | Fnested_using of Id.t * cpp_type  (** Nested using type alias declaration *)
  | Fdeleted_ctor  (** Deleted default constructor: ctor() = delete *)
  | Fraw of string  (** Raw C++ field declaration *)

(** Method descriptor record. *)
and method_field = {
  mf_name : Id.t;  (** Method name *)
  mf_tparams : (template_type * Id.t) list;  (** Template parameters *)
  mf_ret_type : cpp_type;  (** Return type *)
  mf_params : (Id.t * cpp_type) list;  (** Parameters *)
  mf_body : cpp_stmt list;  (** Method body *)
  mf_is_const : bool;  (** True if const method *)
  mf_is_static : bool;  (** True if static method *)
  mf_this_pos : int;
      (** Original 0-based position of the [this] argument in the extracted
          function's parameter list. Recursive calls in the method body still
          use the original argument order, so the loopification checker needs
          this to extract the receiver from [CPPglob] calls correctly.
          For most eponymous methods this is [0]. *)
  mf_no_pure : bool;
      (** When true, suppress [__attribute__((pure))] / [constexpr] for this
          method.  Set for methods whose ML return type is monadic — they
          perform side effects even though the C++ return type may look pure
          after type erasure. *)
}

(** {2 Type schemas} *)

(** C++ type schema: number of type variables and the type expression. *)
type cpp_schema = int * cpp_type

(** {2 Helper constructors} *)

(** Construct a shared_ptr type wrapping an inductive type. *)
val ind_ty_ptr : GlobRef.t -> cpp_type list -> cpp_type

(** Rvalue reference type [T&&].  Uses the double-{!Tref} encoding that the
    pretty-printer already handles: [Tref(Tref(t))] prints as [t&&]. *)
val rval_ref : cpp_type -> cpp_type

(** {2 Generic AST traversal combinators}

    These enable writing AST transformations without manually matching every
    constructor. Pass custom cases for the constructors you care about; the
    combinator handles structural recursion for the rest. *)

(** [map_cpp_type f ty] applies [f] to every sub-type in [ty]. Use this to build
    type transformations: pass a function that handles your custom case and
    delegates to [map_cpp_type f] for the recursive case. *)
val map_cpp_type : (cpp_type -> cpp_type) -> cpp_type -> cpp_type

(** [map_expr fe fs ft e] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent. *)
val map_expr :
  (cpp_expr -> cpp_expr) ->
  (cpp_stmt -> cpp_stmt) ->
  (cpp_type -> cpp_type) ->
  cpp_expr ->
  cpp_expr

(** [map_stmt fe fs ft s] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent. *)
val map_stmt :
  (cpp_expr -> cpp_expr) ->
  (cpp_stmt -> cpp_stmt) ->
  (cpp_type -> cpp_type) ->
  cpp_stmt ->
  cpp_stmt

(** [iter_expr_children ~on_expr ~on_stmts e] calls [on_expr] on each
    immediate child expression and [on_stmts] on each immediate child
    statement list of [e]. Does not recurse — the caller controls recursion
    depth through the callbacks. *)
val iter_expr_children :
  on_expr:(cpp_expr -> unit) -> on_stmts:(cpp_stmt list -> unit) ->
  cpp_expr -> unit

(** [iter_stmt_children ~on_expr ~on_stmts s] calls [on_expr] on each
    immediate child expression and [on_stmts] on each immediate child
    statement list of [s]. Does not recurse. For [Smatch], visits the
    scrutinee, extra conditions, reuse condition and statements, and body
    for each branch. For [Scustom_case], visits the scrutinee and branch
    bodies. *)
val iter_stmt_children :
  on_expr:(cpp_expr -> unit) -> on_stmts:(cpp_stmt list -> unit) ->
  cpp_stmt -> unit

(** {2 Top-level declarations} *)

(** C++ top-level declaration. *)
type cpp_decl =
  | Dtemplate of (template_type * Id.t) list * cpp_constraint option * cpp_decl
      (** Template declaration: parameters, optional constraint, inner
          declaration *)
  | Dnspace of GlobRef.t option * cpp_decl list
      (** Namespace with optional reference and declarations *)
  | Dfundef of
      (GlobRef.t * cpp_type list) list
      * cpp_type
      * (Id.t * cpp_type) list
      * cpp_stmt list
      * bool
      (** Function definition: names with type args, return type, parameters,
          body. Bool suppresses pure/constexpr (for monadic functions). *)
  | Dfundecl of
      (GlobRef.t * cpp_type list) list
      * cpp_type
      * (Id.t option * cpp_type) list
      * bool
      (** Function declaration: names with type args, return type, parameters
          (may be unnamed). Bool suppresses pure attribute (for axiom stubs). *)
  | Dstruct of {
      ds_ref : GlobRef.t;  (** Struct reference *)
      ds_fields : (cpp_field * cpp_visibility * section_tag) list;
          (** Fields with visibility *)
      ds_tparams : (template_type * Id.t) list;
          (** Template parameters (empty for non-templates) *)
      ds_constraint : cpp_constraint option;
          (** Optional template constraint *)
      ds_needs_shared_from_this : bool;
          (** True if inherits enable_shared_from_this *)
    }
  | Dstruct_decl of GlobRef.t  (** Forward struct declaration *)
  | Dusing of GlobRef.t * cpp_type  (** Type alias: using name = type *)
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
      (** Global variable definition with initializer *)
  | Ddecl of GlobRef.t * cpp_type  (** Global variable declaration *)
  | Dconcept of GlobRef.t * cpp_expr
      (** Concept definition (template params from outer Dtemplate) *)
  | Dstatic_assert of cpp_expr * string option
      (** Static assertion with optional message *)
  | Denum of {
      de_ref : GlobRef.t;  (** Enum reference *)
      de_ctors : Id.t list;  (** Constructor names *)
      de_ctor_rocq_names : string list;
          (** Original Rocq constructor names for doc comment lookup *)
      de_tparams : (template_type * Id.t) list;  (** Template parameters *)
    }
