(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Target language for extraction: a core C++ called MiniCpp.

    Crane's extraction pipeline has two intermediate representations:

    {[ Rocq CIC --[extraction.ml]--> MiniML --[translation.ml]--> MiniCpp
       --[cpp.ml]--> C++ ]}

    {!Miniml} handles type erasure, signature computation, and ML-level
    optimizations on a language-agnostic functional AST.  MiniCpp (this file)
    captures C++-specific idioms: [shared_ptr] memory management,
    [std::variant], templates, concepts, namespaces, structs with visibility,
    move semantics, enum classes, and constructors.  Every name is
    pre-resolved ({!cpp_name}) and every inductive pre-classified
    ({!cpp_ind_kind}) during {!Translation}, so {!Cpp} — the pretty-printer —
    needs no name-resolution or type-analysis logic of its own.

    See [minicpp.ml] for a detailed explanation of why both representations are
    needed and cannot be merged. *)

open Names

(** {2 Pre-resolved C++ name}

    Computed during translation so the pretty-printer doesn't need
    name-resolution logic. *)

(** A list held in reverse of the order it is written in.

    [CPPlambda] stores its parameters, and [CPPfun_call] its arguments, this
    way.  The type is private, so a plain list cannot be passed off as one:
    build with {!mk_lambda} or {!mk_call} from a list in source order, or,
    where a reversed list is genuinely what is in hand, say so with
    {!of_reversed}.  Reading is unrestricted -- a [revd] pattern-matches and
    iterates as the list it is. *)
type 'a revd = private {rev : 'a list}

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
  | Tinstance of Id.t * GlobRef.t
      (** A type-class instance template parameter ([_tcI0]) and the class
          constraining it.  Types qualified under it ([typename _tcI0::M]) are
          dependent — see {!instance_dependent}. *)
  | Tpromoted of Id.t
      (** A [Type]-valued type-class field, lifted to an associated type.
          Carries only its name: which instance it hangs off is decided later,
          by substituting a resolution map. *)
  | Tid of Id.t * cpp_type list
      (** Local type identifier with type arguments, for nested structs *)
  | Tid_external of string * cpp_type list
      (** A named type emitted verbatim, never struct-qualified (unlike
          {!Tid}): a type from an included header, a builtin scalar, or a
          struct local to a function body.  The name is a [string] rather than
          an [Id.t] because it is C++ text, not a Rocq identifier: several of
          these carry a qualified name such as [std::invoke_result_t]. *)
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
  | Tapply of cpp_type * cpp_type list
      (** An alias template applied to arguments: [typename I::template C<A>]
          when the head is an associated type, [C<A>] otherwise. *)
  | Tref of cpp_type  (** C++ reference type *)
  | Tptr of cpp_type  (** C++ pointer type *)
  | Tvariant of cpp_type list  (** std::variant<...> for sum types *)
  | Tshared_ptr of cpp_type  (** std::shared_ptr<T> for managed memory *)
  | Tvoid  (** void type *)
  | Tunresolved
      (** No C++ type was determined for this position.  Distinct from
          {!Miniml.Tunknown}, which is the ML-level bottom: this one is
          produced by the back end, notably by {!Loopify} when a call frame
          is built before the types of the values it saves are known.

          Consumers must resolve it -- to a real type, or to [Tauto] where C++
          can deduce one.  Reaching the printer is an anomaly: there is no C++
          spelling for it. *)
  | Tany  (** std::any for type-erased storage of existentials *)
  | Ttyctor of cpp_type
      (** A type constructor named but not applied, as required at a template
          template argument position ([holder<std::optional>]): prints as the
          head of the wrapped type, with its argument list dropped. *)
  | Topaque
      (** A type whose C++ representation is not known here.  Prints as
          [std::any] just as {!Tany} does, but carries the opposite claim:
          {!Tany} asserts the value is physically boxed and so licenses boxing
          and [any_cast], while [Topaque] admits ignorance and licenses
          neither.  Consumers that must act fall back on the
          representation-tolerant helpers in [crane_fn.h].  It survives only in
          an expression's inferred type; at a declaration or storage position
          [materialise_opaque] turns it into {!Tany}, since writing [std::any]
          there is what makes the value boxed. *)
  | Tauto
      (** auto for phantom tvar positions where C++ cannot deduce the type *)
  | Tdecltype of cpp_expr  (** decltype(expr) for deduced types *)
  | Tdecay of cpp_type  (** std::decay_t<T> - strips references/cv from template params *)

(** Type metavariable for unification. *)
and cpp_meta = {
  id : int;  (** Unique identifier *)
  mutable contents : cpp_type option;
      (** Unification result, None if unresolved *)
}

(** {2 C++ statements} *)

(** Whether an assignment also declares its target.  This used to be a
    [cpp_type option], where [None] read as "no type annotation" but in fact
    meant "not a declaration at all" -- an unannotated declaration is
    [Declare Tauto]. *)
and asgn_target =
  | Declare of cpp_type
      (** [ty x = e;] -- a declaration with an initialiser; [Tauto] gives
          [auto x = e;]. *)
  | Existing  (** [x = e;] -- [x] is already in scope. *)

(** C++ statement representation. *)
and cpp_stmt =
  | Sreturn of cpp_expr option  (** Return statement with optional expression *)
  | Sdecl of Id.t * cpp_type  (** Variable declaration *)
  | Sasgn of Id.t * asgn_target * cpp_expr
      (** Assignment to a variable, declaring it or not: see
          {!asgn_target}. *)
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
  | Sif_constexpr of cpp_expr * cpp_stmt list * cpp_stmt list
      (** [if constexpr (cond) { ... } else { ... }] -- a branch resolved when
          the enclosing template is instantiated, so only the taken side is
          required to compile. *)
  | Sif_then of cpp_expr * cpp_stmt list
      (** Conditional without an else branch *)
  | Sif_decl of Id.t * cpp_type * cpp_expr * cpp_stmt list * cpp_stmt list
      (** C++17 if-with-declaration: [if (type id = expr) { then } else { else }].
          The declaration doubles as the condition (pointer truthiness). *)
  | Sraw of string  (** Raw C++ code printed verbatim *)
  | Scomment of string  (** Documentation comment, printed as [/// text] *)
  | Sstruct_def of Id.t * (Id.t * cpp_type) list
      (** Local struct definition: struct Name { T1 f1; T2 f2; }; *)
  | Susing of Id.t * cpp_type
      (** Local using alias: using Name = Type; *)
  | Sdecl_init of Id.t * cpp_type
      (** Value-initialized declaration: Type name{}; *)
  | Sassign_field of cpp_expr * Id.t * cpp_expr
      (** Field assignment for in-place mutation during memory reuse *)
  | Sassign_expr of cpp_expr * cpp_expr
      (** General assignment: lhs = rhs *)
  | Sderef_asgn of cpp_expr * cpp_expr
      (** Dereference assignment: [*lhs = rhs].  Used by the
          [shared_ptr<std::function>] fixpoint pattern to assign through
          the pointer indirection, and for [reset()] body: [*this = T()].
          See {!Translation.gen_local_fix_shared_ptr}. *)
  | Sfor_range of Id.t * cpp_expr * cpp_stmt list
      (** Range-based for: [for (auto& id : e) { body }].  The binding is
          always [auto&] -- every producer walks a container in order to move
          out of it. *)
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
  smb_is_value_type : bool;
      (** When [true], the scrutinee is a value type (not shared_ptr). *)
  smb_is_owned : bool;
      (** When [true], the scrutinee is owned.  Owned value types use
          [auto [...] = std::move(std::get<T>(scrut.v_mut()))]. *)
  smb_is_flat : bool;
      (** When [true], flat single-constructor type: bind directly from
          scrutinee, no [std::get] and no [holds_alternative]. *)
  smb_body : cpp_stmt list;
      (** Branch body statements. *)
}

(** {2 C++ expressions} *)

(** C++ expression representation. *)
(** Where an allocation's storage comes from.  These differ only in where the
    cell is taken from and what smart pointer comes back; every one of them is
    the callee of a {!CPPfun_call}. *)
and alloc_kind =
  | Alloc_heap  (** [std::make_shared<T>] / [crane::make_rc<T>] *)
  | Alloc_arena
      (** [crane::arena_alloc<T>]: allocates in the ambient arena and returns
          a raw [T*]. *)
  | Alloc_arena_shared
      (** [crane::arena_shared_alloc<T>]: allocates into [T]'s single
          thread-local shared capsule and returns a [crane::capsule<T>]. *)
  | Alloc_arena_scoped
      (** The arena-aware form of the ordinary factory ([crane::rc<T>::make],
          [crane::arena_make_shared<T>], or plain [make_shared] under BDE).
          Returns the field's own smart-pointer type, and is exactly the plain
          factory when no arena scope is open at the call site. *)
  | Alloc_reusing
      (** [crane::make_rc_reusing<T>] (Perceus reuse): the first argument is a
          reuse token moved from a matched, uniquely-owned recursive child;
          the rest construct the new [T].  Only emitted under
          [Crane NonAtomicRc]. *)

(** What translation knew about a call.

    Translation knows the C++ types of every call it builds -- it has to, to
    decide boxing -- and used to drop them, leaving later passes to
    reconstruct them from the untyped expression.  {!Loopify.infer_saved_type}
    is what that reconstruction looked like for the result: a bottom-up guess
    that fell back on matching the callee's *name string*.  The printer did
    the same for the parameters, re-reading the callee's ML type out of the
    front-end table and re-splitting its arrows.  Carrying the answers is
    cheaper than re-deriving them and cannot disagree with itself.

    Both fields are derived from one instantiated callee type, in
    [Translation.record_call_sig]. *)
and call_sig = {
  cs_yields : call_result;  (** what the call evaluates to *)
  cs_params : call_params;  (** what the callee takes *)
}

(** What a call yields. *)
and call_result =
  | Ryields of cpp_type  (** the call evaluates to a value of this type *)
  | Ropaque
      (** The callee has no Crane-level type: a runtime helper, or a callee
          printed verbatim from a custom extraction string.  A consumer that
          needs a type here must defer to C++ deduction ([auto], [decltype]);
          it must not invent one. *)

(** The callee's parameter types, as C++ spells them. *)
and call_params =
  | Ptypes of cpp_type list
      (** One type per argument, positionally aligned with the call's
          arguments.  Alignment is guaranteed by construction: {!call_sig}
          drops a list whose length does not match the argument count, since
          a misaligned list is worse than none. *)
  | Punknown
      (** The callee's parameter types are not Crane-level types, or are not
          known here. *)

(** How a member name attaches to the object in front of it.  Scope
    resolution is not one of these: [::] takes a namespace or a type, not an
    object, so it is {!CPPscope} rather than a third token here. *)
and obj_access =
  | Adot (** [obj.member] *)
  | Aarrow (** [obj->member] *)

and cpp_expr =
  | CPPvar of Id.t  (** Local variable reference *)
  | CPPglob of GlobRef.t * cpp_type list * custom_info option
      (** Global reference with type arguments and optional custom extraction
          info *)
  | CPPnamespace of GlobRef.t * cpp_expr  (** Namespace-qualified expression *)
  | CPPfun_call of call_sig * cpp_expr * cpp_expr revd
      (** Function call: what translation knew about it, the callee, and its
          arguments (in reverse order, see {!revd}) *)
  | CPPconverting_ctor of cpp_type * cpp_expr list
      (** Converting constructor call: [Type(args)] *)
  | CPPbox of cpp_type * cpp_expr
      (** A value put into a [std::any], spelled at the erased type the box is
          written as — [std::any] itself, or a [using] alias for it.  Prints
          exactly as the converting constructor it is; it is a category of its
          own so that recognising a box is a pattern match rather than a
          question about a type, and so that the two ways of writing one down
          that mean nothing — a box around a box, and a cast applied straight
          to a fresh box — are normalised away at the single place that builds
          them, {!Cpp_erasure.converting_ctor}. *)
  | CPPderef of cpp_expr  (** Pointer dereference *)
  | CPPmove of cpp_expr  (** std::move for move semantics *)
  | CPPforward of cpp_type * cpp_expr
      (** std::forward<T> for perfect forwarding *)
  | CPPlambda of cpp_lambda  (** Lambda: see {!cpp_lambda}. *)
  | CPPvisit  (** std::visit for variant pattern matching *)
  | CPPalloc of alloc_kind * cpp_type
      (** An allocation: see {!alloc_kind}.  Used as the callee of a
          {!CPPfun_call} whose arguments are the constructor arguments. *)
  | CPPoverloaded of cpp_lambda list
      (** Overloaded visitor set for variant matching.  An overload set is
          lambdas and nothing else, so it is typed by {!cpp_lambda}. *)
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
  | CPPthis  (** this pointer in method context *)
  | CPPshared_from_this of cpp_type
      (** std::const_pointer_cast<T>(shared_from_this()) *)
  | CPPaccess of obj_access * cpp_expr * Id.t
      (** Member access: [obj.member] or [obj->member], the token being the
          only difference between the two. *)
  | CPPaccess_call of obj_access * cpp_expr * Id.t * cpp_expr list
      (** The applied form of {!CPPaccess}: object, method name, arguments. *)
  | CPPscope of cpp_expr * Id.t * cpp_type list
      (** Scope resolution: [expr::id], or [expr::template id<tys...>] when
          the type list is non-empty.  Template arguments belong here and
          nowhere else, [.] and [->] having no such form. *)
  | CPPqualified_t of cpp_type * Id.t  (** Type-qualified member: Type::id *)
  | CPPconvertible_to of cpp_type  (** std::convertible_to<T> type trait *)
  | CPPabort of string * cpp_type
      (** A never-returning expression: throws the given message.  The
          {!cpp_type} is what the expression yields, so a printer is never left
          to guess one; an erased slot states {!Tany} rather than defaulting to
          it. *)
  | CPPenum_val of GlobRef.t * Id.t
      (** Enum class value: EnumType::Constructor *)
  | CPPnullptr  (** nullptr literal *)
  | CPPbraced of cpp_expr list  (** Braced initializer: {a, b, ...} *)
  | CPPstd_get of cpp_type * Id.t option * cpp_expr option
      (** [std::get<T>(expr)] or [std::get<typename T::Ctor>(expr)] *)
  | CPPstd_holds_alternative of cpp_type * Id.t option
      (** [std::holds_alternative<T>(...)] or
          [std::holds_alternative<typename T::Ctor>(...)] *)
  | CPPdeclval of cpp_type  (** std::declval<T>() *)
  | CPPis_same of cpp_type * cpp_type
      (** [std::is_same_v<T, U>] -- a compile-time type comparison, so it can
          only be asked inside an {!Sif_constexpr}. *)
  | CPPtypename_qualified of cpp_type * Id.t
      (** typename T::Nested *)
  | CPPlit of cpp_type * string
      (** A literal rendered verbatim, at the type it has.

          Distinct from {!CPPraw}, which is an arbitrary snippet whose type
          nothing knows: a literal is precisely the case where the producer
          does know -- a numeral mapping renders [UINT64_C(1)] through a
          format string it holds alongside the C++ type the numeral inductive
          extracts to.  Spelling the value but dropping the type left
          consumers to guess, and {!Loopify} guessed
          [std::decay_t<decltype(UINT64_C(1))>]. *)
  | CPPraw of string
      (** Raw C++ expression code, from a user-supplied extraction template or
          a snippet Crane assembles as text.  A reference to the Crane runtime
          is a {!CPPrt}, not one of these.  A literal belongs in a
          {!CPPlit}. *)
  | CPPrt of Crane_rt.helper
      (** A Crane runtime helper, named rather than spelled. *)
  | CPPbinop of string * cpp_expr * cpp_expr
      (** Binary operator for reuse optimization conditions *)
  | CPPcond of cpp_expr * cpp_expr * cpp_expr
      (** Ternary conditional: cond ? then_expr : else_expr *)
  | CPPbool of bool  (** Boolean literal: true/false *)
  | CPPint of int  (** Integer literal *)
  | CPPbrace_init  (** Empty brace initialization: {} *)
  | CPPunop of string * cpp_expr  (** Unary operator: !expr, -expr, etc. *)
  | CPPany_cast of cpp_type * cpp_expr
      (** [std::any_cast<T>(expr)] — recovers a typed value from a
          [std::any] at a shape known exactly at codegen time. *)
  | CPPany_cast_tolerant of cpp_type * cpp_expr
      (** [crane_any_cast<T>(expr)] — as {!CPPany_cast}, but the shape the
          value has in the box is only knowable once C++ instantiates the
          surrounding template, so the [crane_fn.h] helper decides.  Produced
          by {!Cpp_erasure.resolve_casts}, never by translation. *)
  | CPPerase_fn of cpp_type option * cpp_expr
  | CPPfn_value of cpp_expr
      (** [std::function(expr)] — gives a callable a nameable type, deduced
          from it by [std::function]'s CTAD.  A closure's own type cannot be
          spelled, so it cannot agree with any other occurrence of the same
          template parameter. *)
  | CPPcontainer_cast of cpp_type * cpp_expr * bool
      (** crane_container_cast<Dst>(expr) — converts a type-erased sequence
          container (element type std::any) into a concrete-element container
          by std::any_cast-ing each element. The bool suppresses [%elem]
          boxing when rendering [Dst], for callees generic over the element. *)
  | CPPstd_get_if of cpp_type * Id.t option * cpp_expr
      (** std::get_if<T>(&variant) — pointer-returning variant accessor.
          Uses [(sn()).get_if] for BDE compatibility. *)

(** A lambda expression.  Named as a record because an overload set
    ({!CPPoverloaded}) is a list of {e lambdas}: the elements' shape is part of
    what an overload set is, so the type says it rather than a comment. *)
and cpp_lambda = {
  cl_params : (cpp_type * Id.t option) revd;
      (** Parameters, reversed -- see {!revd}.  Read them with
          {!lambda_params}. *)
  cl_ret : cpp_type option;  (** Trailing return type, when one is written. *)
  cl_body : cpp_stmt list;
  cl_by_value : bool;  (** A [\[=\]] capture rather than a [\[&\]] one. *)
}

(** Alias for constraint expressions in requires clauses. *)
and cpp_constraint = cpp_expr

(** {2 Template parameters} *)

(** Template parameter kinds. *)
and template_type =
  | TTtypename  (** Plain typename parameter *)
  | TTtypename_default of cpp_type
      (** typename with default: typename T = default_type *)
  | TTtemplate of int
      (** [template <typename, ...> class T] with the given arity.  A Rocq
          parameter of kind [Type -> Type] is applied to arguments in the
          signature it appears in, and a plain [typename] cannot be applied. *)
  | TTfun of (cpp_type list * cpp_type)
      (** Function type parameter for higher-order templates *)
  | TTconcept of GlobRef.t * cpp_type list
      (** Concept-constrained parameter.  The [cpp_type list] carries the
          concept's extra kept type arguments: [] for a unary concept
          ([Eq _tcI0]), or the kept args for a multi-parameter concept
          ([C<_tcI0, T1>]). *)

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
  | Fconstructor of
      (Id.t * cpp_type) list * (Id.t * cpp_expr) list * bool * bool
      (** Constructor: parameters, member initializer list, explicit flag,
          noexcept flag *)
  | Fdestructor of cpp_stmt list  (** Destructor body for the enclosing struct *)
  | Fnested_struct of Id.t * (cpp_field * cpp_visibility * section_tag) list
      (** Nested struct definition with visibility-annotated fields *)
  | Fnested_using of (template_type * Id.t) list * Id.t * cpp_type  (** Nested using type alias declaration *)
  | Fdeleted_ctor  (** Deleted default constructor: ctor() = delete *)
  | Fdefaulted_special_members
      (** Explicitly-defaulted copy/move constructors and assignment operators.
          Emitted alongside a user-declared (iterative-drain) destructor, which
          would otherwise suppress the implicit move operations — turning every
          [std::move] of the value into a refcount-bumping copy and defeating
          move semantics (and Perceus reuse). *)
  | Ftemplate_ctor of
      (template_type * Id.t) list
      * bool
      * (Id.t * cpp_type) list
      * cpp_stmt list
      (** Template converting constructor: template params, explicit flag,
          constructor params, body statements *)

(** Method descriptor record. *)
and method_field = {
  mf_name : Id.t;  (** Method name *)
  mf_tparams : (template_type * Id.t) list;  (** Template parameters *)
  mf_ret_type : cpp_type;  (** Return type *)
  mf_params : (Id.t * cpp_type) list;  (** Parameters *)
  mf_body : cpp_stmt list;  (** Method body *)
  mf_is_const : bool;  (** True if const method *)
  mf_is_static : bool;  (** True if static method *)
  mf_is_inline : bool;  (** True to emit explicit [inline] keyword *)
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
  mf_is_noexcept : bool;
      (** When true, emit [noexcept] after the parameter list.  Set for
          move assignment operators. *)
}

(** Custom extraction metadata for manually mapped entities.  Resolved once
    during translation. *)
and custom_info = {
  ci_inline : string option;
      (** Some code if entity should be inlined, None otherwise *)
  ci_is_custom : bool;  (** True if entity has custom C++ mapping *)
  ci_yields : cpp_type option;
      (** For a [%result] block template used as a value: what the block
          evaluates to, recorded where the global's ML type was still in
          hand.  A block in expression position is printed as an immediately
          invoked lambda, and a lambda has to be given a return type. *)
}

(** {2 Type schemas} *)

(** C++ type schema: number of type variables and the type expression. *)
type cpp_schema = int * cpp_type

(** {2 Helper constructors} *)

(** Construct a shared_ptr type wrapping an inductive type.
    @param id the global reference of the inductive type
    @param vars type arguments to instantiate the inductive
    @return [Tshared_ptr (Tglob (id, vars, []))] *)
val ind_ty_ptr : GlobRef.t -> cpp_type list -> cpp_type

(** Rvalue reference type [T&&].  Uses the double-{!Tref} encoding that the
    pretty-printer already handles: [Tref(Tref(t))] prints as [t&&].
    @param ty the base type to wrap as an rvalue reference
    @return [Tref (Tref ty)] *)
val rval_ref : cpp_type -> cpp_type

(** The instance parameter a type is qualified under, if any: [typename
    _tcI0::M] yields its {!Tinstance} name and class.  Such a type is
    dependent — what it resolves to is a property of the instance C++
    eventually substitutes, so codegen cannot decide it. *)
val instance_dependent : cpp_type -> (Id.t * GlobRef.t) option

(** {2 Generic AST traversal combinators}

    These enable writing AST transformations without manually matching every
    constructor. Pass custom cases for the constructors you care about; the
    combinator handles structural recursion for the rest. *)

(** [map_cpp_type f ty] applies [f] to every sub-type in [ty]. Use this to build
    type transformations: pass a function that handles your custom case and
    delegates to [map_cpp_type f] for the recursive case.
    @param f the transformation to apply at each node
    @param ty the type to transform
    @return the structurally-transformed type *)
val map_cpp_type : (cpp_type -> cpp_type) -> cpp_type -> cpp_type

(** [curry_fun_type ty] respells every multi-parameter function type inside
    [ty] as nested single-parameter ones, as required of a type standing at a
    template argument position. *)
val curry_fun_type : cpp_type -> cpp_type

(** [recurry_to n ty] respells the function type [ty] as one taking [n]
    parameters and returning a curried function of the rest; [n = 0] curries
    throughout. *)
val recurry_to : int -> cpp_type -> cpp_type

(** [subst_cpp_tvars sub ty] replaces every [Tvar (i, _)] in [ty] by [sub i].

    Unlike {!map_cpp_type}, the replacement is not traversed again, so a
    substitution whose image mentions the variable it replaces (the [T1] of
    [list T1] instantiated at [Prod<T1, T2>]) terminates.
    @param sub the replacement for a type variable index, [None] to keep it
    @param ty the type to substitute in
    @return the substituted type *)
val subst_cpp_tvars : (int -> cpp_type option) -> cpp_type -> cpp_type

(** [exists_cpp_type p ty] holds when [p] holds of [ty] itself or of any type
    nested inside it.

    Deliberately limited to {e containment} questions — "is there a
    [shared_ptr] anywhere in here".  A predicate whose answer genuinely differs
    per constructor (whether a type is literal, whether it is worth moving) is
    clearer as an explicit match, and should stay one.
    @param p the predicate tested at each node
    @param ty the type to search
    @return whether any node satisfies [p] *)
val exists_cpp_type : (cpp_type -> bool) -> cpp_type -> bool

(** Whether [ty] mentions a [std::shared_ptr] anywhere, however deeply — as the
    element of a container, a function's argument or result, or the type
    itself.
    @param ty the type to search
    @return whether a [Tshared_ptr] node occurs in [ty] *)
val contains_shared_ptr : cpp_type -> bool

(** {1 The reversal convention}

    [CPPfun_call] stores its arguments, and [CPPlambda] its parameters, in
    reverse order.  That is a property of the representation, not of the
    language being generated, and every site that spells the constructor
    directly has to remember it unaided.  The functions below are the only
    place the reversal should appear: build with {!mk_call} and {!mk_lambda},
    read with {!call_args} and {!lambda_params}, and the lists are in source
    order throughout.  A lambda's parameters carry the {!revd} type, so a
    plain list cannot reach that field except through {!mk_lambda} or the
    explicit {!of_reversed}. *)

(** The underlying list of a {!revd}, still in reverse order.  For
    folds and membership tests where the order does not matter; use
    {!call_args} or {!lambda_params} when it does. *)
val to_reversed : 'a revd -> 'a list

(** A list that is already in reverse order, admitted as one.  Use where the
    reversal is genuinely already done -- threading a sublist of an existing
    call's arguments, say -- and {!mk_call} or {!mk_lambda} everywhere else. *)
val of_reversed : 'a list -> 'a revd

(** [mk_call ?yields fn args] is a call of [fn] on [args] given in {e source}
    order.  [yields] is the call's result type where the builder knows it;
    omitting it means {!Ropaque}, which is a claim -- that the callee has no
    Crane-level type -- and not a shrug.
    Calling a {!CPPabort} with no arguments is that same abort. *)
val call_opaque : call_sig
(** The signature of a call nothing is known about. *)

val call_sig :
  ?yields:cpp_type ->
  ?params:cpp_type list ->
  nargs:int ->
  unit ->
  call_sig
(** [call_sig ?yields ?params ~nargs ()] is what a builder knows about a call
    on [nargs] arguments.  [params] is recorded only when its length matches
    [nargs]: a misaligned list is worse than none, so alignment holds by
    construction rather than by convention. *)

val mk_call :
  ?yields:cpp_type ->
  ?params:cpp_type list ->
  cpp_expr ->
  cpp_expr list ->
  cpp_expr

(** [mk_apply fn args] applies [fn] to [args], given in {e source} order.
    Applying no arguments is [fn] itself, unlike {!mk_call}, where the empty
    list is a nullary call [fn()]. *)
val mk_apply :
  ?yields:cpp_type ->
  ?params:cpp_type list ->
  cpp_expr ->
  cpp_expr list ->
  cpp_expr

(** [mk_lambda params ret body ~by_value] is a lambda whose [params] are given
    in {e source} order.  [by_value] selects a [\[=\]] capture over [\[&\]].
    A nullary lambda whose body only throws reduces to {!CPPabort}, carrying
    [ret] -- or {!Tany} when [ret] is absent -- as the type it yields. *)
val mk_lambda :
  (cpp_type * Id.t option) list ->
  cpp_type option ->
  cpp_stmt list ->
  by_value:bool ->
  cpp_expr

(** [lambda params ret body ~by_value] is {!mk_lambda} as a {!cpp_lambda}, for
    the positions that take a lambda rather than an expression -- an element of
    a {!CPPoverloaded} set.  Parameters are given in {e source} order.  A body
    that only throws cannot reduce to {!CPPabort} here, there being no
    expression position to reduce into. *)
val lambda :
  (cpp_type * Id.t option) list ->
  cpp_type option ->
  cpp_stmt list ->
  by_value:bool ->
  cpp_lambda

(** [mk_iife ret body] evaluates [body] in place: a nullary lambda, invoked
    immediately, capturing by reference.  A body that only throws reduces to
    {!CPPabort} carrying [ret]; a lambda around it would deduce [void] and
    could not stand where a value is expected. *)
val mk_iife : cpp_type option -> cpp_stmt list -> cpp_expr

(** The arguments of a {!CPPfun_call}, in source order. *)
val call_args : cpp_expr revd -> cpp_expr list

(** [map_args f args] rewrites each of a call's arguments with [f], keeping
    them in the order they are stored.  For the many rewriters that descend
    through a call without caring what order its arguments are in. *)
val map_args : (cpp_expr -> cpp_expr) -> cpp_expr revd -> cpp_expr revd

(** The parameters of a {!CPPlambda}, in source order. *)
val lambda_params :
  (cpp_type * Id.t option) revd -> (cpp_type * Id.t option) list

(** [map_lambda fs ft l] maps [ft] over the parameter and return types of [l]
    and [fs] over its body.  A lambda has no immediate sub-expression of its
    own, so there is no expression function to take. *)
val map_lambda :
  (cpp_stmt -> cpp_stmt) -> (cpp_type -> cpp_type) -> cpp_lambda -> cpp_lambda

(** [map_expr fe fs ft e] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent.
    @param fe transformation for immediate child expressions
    @param fs transformation for immediate child statements
    @param ft transformation for immediate child types
    @return the structurally-transformed expression *)
val map_expr :
  (cpp_expr -> cpp_expr) ->
  (cpp_stmt -> cpp_stmt) ->
  (cpp_type -> cpp_type) ->
  cpp_expr ->
  cpp_expr

(** [map_stmt fe fs ft s] applies [fe] to sub-expressions, [fs] to
    sub-statements, [ft] to sub-types, performing one level of structural
    descent.
    @param fe transformation for immediate child expressions
    @param fs transformation for immediate child statements
    @param ft transformation for immediate child types
    @return the structurally-transformed statement *)
val map_stmt :
  (cpp_expr -> cpp_expr) ->
  (cpp_stmt -> cpp_stmt) ->
  (cpp_type -> cpp_type) ->
  cpp_stmt ->
  cpp_stmt

(** [iter_expr_children ~on_expr ~on_stmts e] calls [on_expr] on each
    immediate child expression and [on_stmts] on each immediate child
    statement list of [e]. Does not recurse — the caller controls recursion
    depth through the callbacks.
    @param on_expr callback for each immediate child expression
    @param on_stmts callback for each immediate child statement list *)
val iter_expr_children :
  on_expr:(cpp_expr -> unit) -> on_stmts:(cpp_stmt list -> unit) ->
  cpp_expr -> unit

(** [iter_stmt_children ~on_expr ~on_stmts s] calls [on_expr] on each
    immediate child expression and [on_stmts] on each immediate child
    statement list of [s]. Does not recurse. For [Smatch], visits the
    scrutinee, extra conditions, reuse condition and statements, and body
    for each branch. For [Scustom_case], visits the scrutinee and branch
    bodies.
    @param on_expr callback for each immediate child expression
    @param on_stmts callback for each immediate child statement list *)
val iter_stmt_children :
  on_expr:(cpp_expr -> unit) -> on_stmts:(cpp_stmt list -> unit) ->
  cpp_stmt -> unit

(** [fold_expr_children ~on_expr ~on_stmts acc e] folds over the immediate
    children of [e], threading [acc].  Mirrors {!iter_expr_children}: [on_expr]
    folds over child expressions and [on_stmts] over child statement lists
    (e.g. a [CPPlambda] body), so lambda bodies are not silently skipped.
    @param on_expr fold step for each immediate child expression
    @param on_stmts fold step for each immediate child statement list
    @param acc the initial accumulator value
    @return the final accumulator after visiting all children *)
val fold_expr_children :
  on_expr:('a -> cpp_expr -> 'a) -> on_stmts:('a -> cpp_stmt list -> 'a) ->
  'a -> cpp_expr -> 'a

(** [fold_stmt_children ~on_expr ~on_stmts acc s] folds over the immediate
    children of [s], threading [acc].  Mirrors {!iter_stmt_children}.
    @param on_expr fold step for each immediate child expression
    @param on_stmts fold step for each immediate child statement list
    @param acc the initial accumulator value
    @return the final accumulator after visiting all children *)
val fold_stmt_children :
  on_expr:('a -> cpp_expr -> 'a) -> on_stmts:('a -> cpp_stmt list -> 'a) ->
  'a -> cpp_stmt -> 'a

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
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
      (** Global variable definition with initializer *)
  | Dconcept of GlobRef.t * cpp_expr
      (** Concept definition (template params from outer Dtemplate) *)
  | Dstatic_assert of cpp_expr * string option
      (** Static assertion with optional message *)
  | Dusing of GlobRef.t * cpp_type
      (** [using name = ty;]: a second spelling of a type that already exists,
          as when a definition is nothing but another instance's name. *)
  | Denum of {
      de_ref : GlobRef.t;  (** Enum reference *)
      de_ctors : Id.t list;  (** Constructor names *)
      de_ctor_rocq_names : string list;
          (** Original Rocq constructor names for doc comment lookup *)
      de_tparams : (template_type * Id.t) list;  (** Template parameters *)
    }

(** [map_field fe fs ft f] applies [fe] to sub-expressions, [fs] to
    sub-statements and [ft] to sub-types of a visibility-annotated field,
    performing one level of structural descent.  Nested structs recurse. *)
val map_field :
  (cpp_expr -> cpp_expr) -> (cpp_stmt -> cpp_stmt) -> (cpp_type -> cpp_type) ->
  cpp_field * cpp_visibility * section_tag ->
  cpp_field * cpp_visibility * section_tag

(** [map_decl fe fs ft d] applies [fe] to sub-expressions, [fs] to
    sub-statements and [ft] to sub-types of a declaration, including every
    position a type is {e written down} in the generated header.  Nested
    declarations ({!Dtemplate}, {!Dnspace}) recurse.

    This is the rung that lets a whole-declaration pass be written as its three
    leaf functions rather than as a fresh traversal of all nine constructors. *)
val map_decl :
  (cpp_expr -> cpp_expr) -> (cpp_stmt -> cpp_stmt) -> (cpp_type -> cpp_type) ->
  cpp_decl -> cpp_decl
