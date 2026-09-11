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
    shared_ptr memory management, std::variant for inductives,
    templates, concepts, namespaces, structs with visibility, move semantics,
    const/static/extern modifiers, constructors, methods, enum classes, and raw
    C++ escape hatches. The MiniML-to-MiniCpp translation resolves how each
    functional programming pattern maps to C++ idioms (e.g. MLcase becomes
    an if/else-if chain over the variant, MLcons becomes a factory function
    returning shared_ptr, modules become structs, module types become concepts).

    Attempting to go directly from Rocq CIC to MiniCpp would require combining
    type erasure, optimization, and C++ idiom selection into a single pass —
    losing the optimization opportunities that MiniML provides and coupling Rocq
    internals directly to C++ generation. *)

open Names

(** A list held in reverse of the order it is written in.

    [CPPlambda] stores its parameters, and [CPPfun_call] its arguments, this
    way.  Outside this module the type is private, so a plain list cannot be
    passed off as one: build with {!mk_lambda} or {!mk_call} from a list in
    source order, or, where a reversed list is genuinely what is in hand, say
    so with {!of_reversed}. *)
type 'a revd = {rev : 'a list}

(** {2 Inductive classification}

    Determined once during translation. *)

(** Classification of an inductive type for C++ code generation. *)
type cpp_ind_kind =
  | IK_Standard (* std::variant sum type *)
  | IK_Enum (* enum class *)
  | IK_Record of GlobRef.t option list (* struct with named fields *)
  | IK_Eponymous of GlobRef.t option list (* record merged into module *)
  | IK_TypeClass of GlobRef.t option list (* C++ concept *)

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

type cpp_type =
  | Tvar of int * Id.t option
  | Tinstance of Id.t * GlobRef.t
    (* A type-class instance template parameter ([_tcI0]) and the class it is
       constrained by.  Types qualified under it ([typename _tcI0::M]) are
       dependent: what they resolve to is only known when C++ instantiates the
       enclosing template with a particular instance. *)
  | Tpromoted of Id.t
    (* A [Type]-valued field of a type class, lifted from value level to type
       level: it becomes an associated type rather than a struct member.  The
       name alone is carried; which instance it hangs off is only known once a
       resolution map is in scope, so until then it is neither a template
       parameter nor a qualified type. *)
  | Tid of Id.t * cpp_type list
    (* Simple Id-based type, for local names like nested structs *)
  | Tid_external of string * cpp_type list
    (* A named type that is never struct-qualified, unlike [Tid]: a type from
       an included header, a builtin scalar, or a struct local to a function
       body.  The name is C++ text, emitted verbatim. *)
  | Tglob of GlobRef.t * cpp_type list * cpp_expr list
  | Tfun of cpp_type list * cpp_type
  | Tconst of cpp_type
  | Tnamespace of GlobRef.t * cpp_type
  | Tqualified of
      cpp_type * Id.t (* typename Base<T>::nested - for nested struct access *)
  | Tapply of cpp_type * cpp_type list
      (* An alias template applied to arguments: [typename I::template C<A>]
         when the head is an associated type, [C<A>] otherwise.  This is how a
         higher-kinded class parameter ([M : Type -> Type]) is used, the head
         being the instance's associated alias template. *)
  | Tref of cpp_type
  | Tptr of cpp_type
  | Tvariant of cpp_type list
  | Tshared_ptr of cpp_type
  | Tvoid
  | Tunresolved (* no C++ type determined; should not reach the printer *)
  | Tany (* std::any - for type-erased storage of existential types *)
  | Ttyctor of cpp_type
    (* A type constructor named but not applied, as required at a template
       template argument position ([holder<std::optional>]).  Prints as the
       head of [cpp_type] with its argument list dropped. *)
  | Topaque
    (* A type whose C++ representation is not known here.  Prints as
       [std::any], like [Tany], but the two must not be confused: [Tany] is a
       claim that the value *is* physically boxed, and so licenses boxing it
       and casting it back out, whereas [Topaque] is an admission that we do
       not know.  Nothing may box or cast on the strength of [Topaque] alone;
       code that must act falls back on the representation-tolerant helpers in
       [crane_fn.h].  It survives only in the inferred type of an expression:
       at a declaration or storage position, writing [std::any] is what makes
       a value boxed, so [materialise_opaque] turns it into [Tany] there. *)
  | Tauto (* auto - for phantom tvar positions where C++ cannot deduce the type *)
  | Tdecltype of cpp_expr (* decltype(expr) *)
  | Tdecay of cpp_type (* std::decay_t<T> - strips references/cv from template params *)

(** C++ type meta-variable for unification. *)
and cpp_meta = {
  id : int;
  mutable contents : cpp_type option;
}

(* Whether an assignment also declares its target: [Declare ty] prints
   [ty x = e;] (Tauto for [auto]), [Existing] prints [x = e;] for a variable
   already in scope. *)
and asgn_target =
  | Declare of cpp_type
  | Existing

(** C++ statements. *)
and cpp_stmt =
  | Sreturn of cpp_expr option
  | Sdecl of Id.t * cpp_type
  | Sasgn of Id.t * asgn_target * cpp_expr
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
  | Sassert of precondition (* a Rocq precondition, checked or merely stated *)
  | Sif of cpp_expr * cpp_stmt list * cpp_stmt list
  | Sif_constexpr of cpp_expr * cpp_stmt list * cpp_stmt list
    (* if-else: condition, then-branch, else-branch. An empty else-branch
       prints as an [if] with no [else]. *)
  | Sif_decl of Id.t * cpp_type * cpp_expr * cpp_stmt list * cpp_stmt list
    (* C++17 if-with-declaration: [if (type id = expr) { then } else { else }].
       The declaration doubles as the condition (e.g. pointer truthiness).
       Used for [if (auto *_alt = std::get_if<Ctor>(&_v)) { ... }]. *)
  | Sraw of string
    (* Raw C++ code, printed verbatim. Used for low-level operations in reuse
       optimization. *)
  | Scomment of string
    (* Documentation comment, printed as [/// text]. *)
  | Sstruct_def of Id.t * (Id.t * cpp_type) list
    (* Local struct definition: struct Name { T1 f1; T2 f2; }; *)
  | Susing of Id.t * cpp_type
    (* Local using alias: using Name = Type; *)
  | Sdecl_init of Id.t * cpp_type
    (* Value-initialized declaration: Type name{}; *)
  | Sassign_expr of cpp_expr * cpp_expr
  (* Assignment [lhs = rhs;] to anything addressable: a field ([CPPget]), a
     dereferenced pointer ([CPPderef]), or any other lvalue expression. *)
  | Sfor_range of Id.t * cpp_expr * cpp_stmt list
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
  | Smatch of smatch_scrutinee * smatch_branch list * cpp_stmt list option
    (* If/else-if pattern match chain using std::holds_alternative and std::get.
       Branches are checked in order. The optional else body is [Some stmts] for
       a wildcard/default case, or [None] to emit std::unreachable(). *)

(** The value an [Smatch] dispatches on, and how its payload is reached. *)
and smatch_scrutinee = {
  sc_expr : cpp_expr;
    (** Variant accessor expression, e.g. [scrut->v()] or [scrut.v()]. *)
  sc_access : obj_access;
    (** Whether the object under the accessor is reached with [.] or [->]. *)
  sc_owned : bool;
    (** When [true], the scrutinee is owned (last use or explicit move), so the
        payload is taken from [v_mut()] by [auto&] and its fields may be moved
        out.  A borrowed scrutinee reads [v()] through [const auto&]. *)
  sc_flat : bool;
    (** When [true], the type is a flat single-constructor inductive (no variant
        wrapper). The binding uses [const auto& [...] = scrut] directly instead
        of [std::get<Ctor>(scrut.v())]. No [holds_alternative] check is
        emitted. *)
}

(** A branch in an [Smatch] if/else-if pattern match chain. *)
and smatch_branch = {
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
  smb_body : cpp_stmt list;
    (** Branch body statements.  When {!smb_field_bindings} is non-empty,
        field accesses use direct [CPPvar binding_name] references. *)
}

(* A precondition carried over from a Rocq annotation.  Either it has a C++
   spelling and is checked at run time, or it has none and is only stated in a
   comment.  There is no third state: no assertion goes out without saying
   what it asserts, and no "always true" stands in for an absent check. *)
and precondition =
  | Pchecked of string  (* the C++ predicate, which is also its own statement *)
  | Pstated of string  (* the statement alone, for a predicate C++ cannot spell *)

(* The C++ binary operators Crane emits.  A closed set, so that the printer
   cannot be handed an operator it has no spelling for. *)
and cpp_binop =
  | Beq  (* == *)
  | Bneq  (* != *)
  | Band  (* && *)
  | Bor  (* || *)
  | Bassign
    (* = in expression position (a for-loop step, a comma expression).  A
       statement-position assignment is an [Sassign_expr]. *)

(* The C++ unary operators Crane emits. *)
and cpp_unop =
  | Unot  (* ! *)
  | Uaddr  (* & -- take the address, or declare a by-reference capture *)

(* Where an allocation's storage comes from.  Each kind is used the same way:
   as the callee of a CPPfun_call whose arguments are the constructor's. *)
and alloc_kind =
  | Alloc_heap
    (* std::make_shared<T> / crane::make_rc<T>. *)
  | Alloc_arena_scoped
    (* The ordinary-smart-pointer factory that is *arena-aware at runtime* --
       [crane::rc<T>::make] under NonAtomicRc, [crane::arena_make_shared<T>]
       under std, or plain [make_shared] under BDE (no runtime arena there).
       Returns the same smart-pointer type as the field; when no arena scope
       is open at the call site it is exactly the plain make_shared/make_rc. *)
  | Alloc_reusing
    (* crane::make_rc_reusing<T> (Perceus reuse): the first argument is a
       reuse token (a [crane::rc<T>] moved from a matched, uniquely-owned
       recursive child), the rest construct the new T.  Recycles the token's
       cell in place when it is the sole owner, else allocates.  Only emitted
       under [Crane NonAtomicRc] (needs crane::rc's control block). *)

(** C++ expressions. *)
(** What translation knew about a call; see [minicpp.mli]. *)
and call_sig = {
  cs_yields : call_result;
  cs_params : call_params;
}

and call_result =
  | Ryields of cpp_type
  | Ropaque

and call_params =
  | Ptypes of cpp_type list
  | Punknown

(** How a member name attaches to the object in front of it.  Scope
    resolution is not one of these: [::] takes a namespace or a type, not an
    object, so it is {!CPPscope} rather than a third token here. *)
and obj_access =
  | Adot (** [obj.member] *)
  | Aarrow (** [obj->member] *)

and cpp_expr =
  | CPPvar of Id.t
  | CPPglob of GlobRef.t * cpp_type list * custom_info option
  | CPPnamespace of GlobRef.t * cpp_expr
  | CPPfun_call of call_sig * cpp_expr * cpp_expr revd
  | CPPconverting_ctor of cpp_type * cpp_expr list
    (** Converting constructor call: [Type(args)]. Used in clone-field
        conversions where the destination type differs from the source. *)
  | CPPbox of cpp_type * cpp_expr
    (** A value put into a [std::any], spelled at the erased type the box is
        written as ([std::any] itself, or a [using] alias for it).  Prints
        exactly as the converting constructor it is, but boxing is a category
        of its own so that recognising one is a pattern rather than a question
        about a type.  Built only by {!Cpp_erasure.converting_ctor}. *)
  | CPPderef of cpp_expr
  | CPPmove of cpp_expr
  | CPPforward of cpp_type * cpp_expr
  | CPPlambda of cpp_lambda
  | CPPalloc of alloc_kind * cpp_type
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
  | CPPconcept_app of GlobRef.t * GlobRef.t * cpp_type list
  (* Concept<Subject, Args...> -- a concept applied to a named subject and
     further type arguments.  A boolean expression, not a type. *)
  | CPPnew of cpp_type * cpp_expr list (* new Type(args) or new Type{args} *)
  | CPPshared_ptr_ctor of cpp_type * cpp_expr (* std::shared_ptr<T>(expr) *)
  | CPPthis (* this pointer in methods *)
  | CPPshared_from_this of cpp_type
    (* std::const_pointer_cast<T>(shared_from_this()) — for returning this as
       shared_ptr *)
  | CPPaccess of obj_access * cpp_expr * Id.t (* obj.member or obj->member *)
  | CPPaccess_call of obj_access * cpp_expr * Id.t * cpp_expr list
    (* obj.method(args) or obj->method(args) *)
  | CPPscope of cpp_expr * Id.t * cpp_type list
    (* expr::id, or expr::template id<tys...> when the list is non-empty *)
  | CPPqualified_t of
      cpp_type * Id.t (* Type::id - for type-qualified member access *)
  | CPPconvertible_to of cpp_type (* std::convertible_to<T> constraint *)
  | CPPabort of string * cpp_type
      (* never returns: throws [string].  The type is what the expression
         yields, so a printer never has to guess one *)
  | CPPenum_val of
      GlobRef.t * Id.t (* enum class value: EnumType::Constructor *)
  | CPPnullptr (* nullptr *)
  | CPPbraced of cpp_expr list (* braced initializer: {a, b, ...} *)
  | CPPstd_get of cpp_type * cpp_expr option
    (* std::get<T>(expr), std::get<typename T::Ctor>(expr), or bare *)
  | CPPstd_holds_alternative of cpp_type
    (* std::holds_alternative<T>(…) or std::holds_alternative<typename T::Ctor>(…) *)
  | CPPdeclval of cpp_type
  | CPPis_same of cpp_type * cpp_type
    (* std::declval<T>() *)
  | CPPtype_name of cpp_type
    (* typename T::Nested, usable where a dependent nested struct name is
       required as an expression/type-name token. *)
  | CPPlit of cpp_type * string
    (* A literal rendered verbatim, at the type it has. *)
  | CPPraw of string
  | CPPrt of Crane_rt.helper
    (* Raw C++ expression, printed verbatim. Used for low-level operations
       (e.g., literal "1" for use_count check). *)
  | CPPbinop of cpp_binop * cpp_expr * cpp_expr
    (* Binary operator applied to two operands. *)
    (* Pair of two sub-expressions, used internally by loopify to thread
       two values through a single expression slot.  Never reaches the printer. *)
  | CPPcond of cpp_expr * cpp_expr * cpp_expr
    (* Ternary conditional: cond ? then_expr : else_expr. *)
  | CPPbool of bool (* true / false literal *)
  | CPPint of int (* integer literal *)
  | CPPunop of cpp_unop * cpp_expr (* unary operator applied to one operand *)
  | CPPany_cast of cpp_type * cpp_expr
    (* std::any_cast<T>(expr) — recovers a typed value from std::any at a
       shape known exactly here *)
  | CPPany_cast_tolerant of cpp_type * cpp_expr
    (* crane_any_cast<T>(expr) — same, but the shape in the box is only
       knowable when C++ instantiates the surrounding template *)
  | CPPerase_fn of cpp_type option * cpp_expr
    (* crane_erase_fn<Ret>(expr) — adapts a concrete callable to the canonical
       erased representation std::function<Ret(std::any...)>.  [None] means the
       result is erased too (Ret = std::any); [Some t] keeps the codomain, for
       a consumer that erases only the argument types. *)
  | CPPfn_value of cpp_expr
    (* std::function(expr) — gives a callable a nameable type, deduced from
       it by std::function's CTAD.  A closure's own type cannot be spelled,
       so it cannot agree with any other occurrence of the same template
       parameter; wrapping it here is what lets template argument deduction
       succeed. *)
  | CPPcontainer_cast of cpp_type * cpp_expr * bool
    (* crane_container_cast<Dst>(expr) — converts a type-erased sequence
       container (element type std::any) into a concrete-element container by
       [std::any_cast]-ing each element.  Used when an erased list/deque leaf is
       forwarded into a consumer whose parameter has a concrete element type and
       the container type (e.g. std::deque) has no element-converting ctor.
       The bool suppresses [%elem] boxing when rendering [Dst]: set when the
       callee is generic over the element (its own declared signature never
       boxes, since a bare type variable never recurses), so [Dst] must match
       that unboxed declaration rather than this call site's concrete,
       possibly-recursive substituted element type. *)
  | CPPstd_get_if of cpp_type * cpp_expr
    (* std::get_if<T>(&variant) — pointer-returning variant accessor.
       Uses (sn()).get_if for BDE compatibility.  When [Id.t option] is
       [Some id], emits [std::get_if<typename T::Id>(&expr)]. *)

(** A lambda expression. *)
and cpp_lambda = {
  cl_params : (cpp_type * Id.t option) revd;
      (** Parameters, reversed -- see {!revd}.  Read them with
          {!lambda_params}. *)
  cl_ret : cpp_type option;  (** Trailing return type, when one is written. *)
  cl_body : cpp_stmt list;
  cl_by_value : bool;  (** A [\[=\]] capture rather than a [\[&\]] one. *)
}

(** A C++ constraint expression (used in requires clauses). *)
and cpp_constraint = cpp_expr

(** Template parameter kinds. *)
and template_type =
  | TTtypename
  | TTtypename_default of cpp_type (* typename T = default_type *)
  | TTtemplate of int
      (* [template <typename, ...> class T] with the given arity.  A Rocq
         parameter of kind [Type -> Type] is applied to arguments in the
         signature it appears in, and a plain [typename] cannot be applied. *)
  | TTfun of (cpp_type list * cpp_type)
  | TTconcept of GlobRef.t * cpp_type list
      (* Concept-constrained parameter.  The [cpp_type list] holds the concept's
         extra (kept) type arguments beyond the constrained parameter itself:
         [] for a unary concept such as ['Eq T' -> Eq _tcI0], and the kept args
         for a multi-parameter concept such as ['C<I,T>' -> C<_tcI0, T1>]. *)

(** Struct/class field declarations. *)
and cpp_field =
  | Fvar of Id.t * cpp_type
  | Fvar' of GlobRef.t * cpp_type
  | Fmethod of method_field
  (* Private constructor: params, initializer list (as stmts for v_(x) style) *)
  | Fconstructor of
      (Id.t * cpp_type) list
      * (Id.t * cpp_expr) list
      * bool (* explicit *)
      * bool (* noexcept *)
  | Fdestructor of cpp_stmt list
    (* Destructor body for the enclosing struct. *)
  (* Nested struct with its own visibility-annotated fields *)
  | Fnested_struct of Id.t * (cpp_field * cpp_visibility * section_tag) list
  (* Nested using declaration.  The template parameters are empty for a plain
     alias and non-empty for an alias template ([template <typename A> using C
     = List<A>;]), which is how an instance provides the carrier of a
     higher-kinded class parameter. *)
  | Fnested_using of (template_type * Id.t) list * Id.t * cpp_type
  (* Deleted default constructor: ctor() = delete *)
  | Fdeleted_ctor
  (* Explicitly-defaulted copy/move ctors and assignment operators, emitted
     next to a user-declared destructor so the implicit move operations are not
     suppressed (which would make every std::move a refcount-bumping copy). *)
  | Fdefaulted_special_members
  (* Template converting constructor: template params, explicit flag,
     constructor params, body statements *)
  | Ftemplate_ctor of
      (template_type * Id.t) list
      * bool (* explicit *)
      * (Id.t * cpp_type) list
      * cpp_stmt list

(** Method field descriptor for struct methods. *)
and method_field = {
  mf_name : Id.t;
  mf_tparams : (template_type * Id.t) list;
  mf_ret_type : cpp_type;
  mf_params : (Id.t * cpp_type) list;
  mf_body : cpp_stmt list;
  mf_is_const : bool;
  mf_is_static : bool;
  mf_is_inline : bool;
  mf_this_pos : int;
  mf_no_pure : bool;
  mf_is_noexcept : bool;
}

(** Custom extraction info, resolved once during translation. *)
and custom_info = {
  ci_inline : string option; (* Some code if to_inline, None otherwise *)
  ci_is_custom : bool;
  (* For a [%result] block template used as a value: what the block evaluates
     to, recorded while the global's ML type was still in hand. *)
  ci_yields : cpp_type option;
}

(** C++ type schema. The integer is the number of variables in the schema. *)
type cpp_schema = int * cpp_type

(** Construct a shared_ptr type wrapping an inductive type (for recursive
    self-references in constructor fields). Using shared_ptr keeps the value type
    copyable without deep-clone machinery. *)
let ind_ty_ptr id vars = Tshared_ptr (Tglob (id, vars, []))

(** A plain static member function: no template parameters, no [this], and
    none of the qualifiers a real method carries.  Factory functions are the
    only producer -- they are methods with every flag off, so they are
    spelled as methods rather than as a second, near-identical field kind. *)
let static_fun ~name ~ret ~params ~body =
  { mf_name = name;
    mf_tparams = [];
    mf_ret_type = ret;
    mf_params = params;
    mf_body = body;
    mf_is_const = false;
    mf_is_static = true;
    mf_is_inline = false;
    mf_this_pos = 0;
    mf_no_pure = false;
    mf_is_noexcept = false }

(** Rvalue reference type [T&&].  Uses the double-{!Tref} encoding that the
    pretty-printer already handles: [Tref(Tref(t))] prints as [t&&]. *)
let rval_ref ty = Tref (Tref ty)

(** The instance parameter a type is qualified under, if any: [typename
    _tcI0::M] (and longer chains like [typename _tcI0::M::inner]) yield the
    instance and its class.  Such a type is dependent — what it resolves to is
    a property of the instance C++ eventually substitutes, so codegen cannot
    decide it. *)
let rec instance_dependent = function
  | Tqualified (base, _) | Tapply (base, _) -> instance_dependent base
  | Tinstance (id, class_ref) -> Some (id, class_ref)
  | _ -> None

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
  | Tconst t -> Tconst (map_cpp_type f t)
  | Tshared_ptr t -> Tshared_ptr (map_cpp_type f t)
  | Tref t -> Tref (map_cpp_type f t)
  | Tptr t -> Tptr (map_cpp_type f t)
  | Tvariant ts -> Tvariant (List.map (map_cpp_type f) ts)
  | Tnamespace (r, t) -> Tnamespace (r, map_cpp_type f t)
  | Tqualified (t, id) -> Tqualified (map_cpp_type f t, id)
  | Tapply (t, ts) -> Tapply (map_cpp_type f t, List.map (map_cpp_type f) ts)
  | Tdecltype _ -> ty (* decltype wraps CPPraw, no sub-types to map *)
  | Tdecay t -> Tdecay (map_cpp_type f t)
  (* [Ttyctor] is a leaf: only its head is printed, so rewriting inside it
     (erasing an argument to [std::any], say) could only make it unprintable. *)
  | Ttyctor _
  | Tvar _ | Tinstance _ | Tpromoted _ | Tvoid | Tunresolved | Tany | Topaque
  | Tauto -> ty

(** [curry_fun_type ty] respells every multi-parameter function type inside
    [ty] as nested single-parameter ones: [Nat(Nat, Nat)] becomes
    [std::function<Nat(Nat)>(Nat)].

    Crane's calling convention flattens a chain of Rocq arrows into one
    multi-parameter function, which is what a {e definition} wants.  A type
    standing at a template argument position cannot be flattened: a signature
    that rebuilds an arrow out of separate template parameters ([F<function<B
    (A)>>]) spells it one argument at a time, so an instantiation has to as
    well or the two do not match. *)
let curry_fun_type ty =
  map_cpp_type
    (function
      | Tfun (a :: (_ :: _ as rest), cod) -> Tfun ([a], Tfun (rest, cod))
      | t -> t )
    ty

(** [recurry_to n ty] respells the function type [ty] as one taking [n]
    parameters and returning a curried function of whatever is left, using
    {!curry_fun_type} for the remainder.  [n = 0] curries throughout, which is
    what a position declared as a bare type variable asks for.

    Substituting a concrete function type into a codomain that was a type
    variable flattens arrows belonging to the {e element} type into the
    callable's own parameter list.  [n] is the arity the declaration was
    written at, so this restores the shape the signature actually has. *)
let recurry_to n ty =
  match ty with
  | Tfun (dom, cod) when n > 0 && List.length dom > n ->
    let outer = List.filteri (fun i _ -> i < n) dom in
    let inner = List.filteri (fun i _ -> i >= n) dom in
    Tfun (outer, curry_fun_type (Tfun (inner, cod)))
  | _ -> if n = 0 then curry_fun_type ty else ty

(** [subst_cpp_tvars sub ty] replaces every [Tvar (i, _)] in [ty] by
    [sub i], leaving the substituted type alone.

    Unlike {!map_cpp_type}, the replacement is {e not} traversed again, so a
    substitution whose image mentions the variable it replaces (the [T1] of
    [list T1] instantiated at [Prod<T1, T2>]) terminates. *)
let rec subst_cpp_tvars (sub : int -> cpp_type option) (ty : cpp_type) : cpp_type =
  let go = subst_cpp_tvars sub in
  match ty with
  | Tvar (i, _) -> ( match sub i with Some t -> t | None -> ty )
  | Tglob (r, tys, args) -> Tglob (r, List.map go tys, args)
  | Tid (id, tys) -> Tid (id, List.map go tys)
  | Tid_external (id, tys) -> Tid_external (id, List.map go tys)
  | Tfun (dom, cod) -> Tfun (List.map go dom, go cod)
  | Tconst t -> Tconst (go t)
  | Tshared_ptr t -> Tshared_ptr (go t)
  | Tref t -> Tref (go t)
  | Tptr t -> Tptr (go t)
  | Tvariant ts -> Tvariant (List.map go ts)
  | Tnamespace (r, t) -> Tnamespace (r, go t)
  | Tqualified (t, id) -> Tqualified (go t, id)
  | Tapply (t, ts) -> Tapply (go t, List.map go ts)
  | Tdecay t -> Tdecay (go t)
  | Ttyctor _ | Tdecltype _ | Tinstance _ | Tpromoted _ | Tvoid | Tunresolved
  | Tany | Topaque | Tauto -> ty

(** [exists_cpp_type p ty] holds when [p] holds of [ty] itself or of any type
    nested inside it.

    Deliberately limited to {e containment} questions — "is there a
    [shared_ptr] anywhere in here".  A predicate whose answer genuinely differs
    per constructor (whether a type is literal, whether it is worth moving) is
    clearer as an explicit match, and should stay one. *)
let rec exists_cpp_type (p : cpp_type -> bool) (ty : cpp_type) : bool =
  p ty
  ||
  match ty with
  | Tglob (_, tys, _) | Tid (_, tys) | Tid_external (_, tys) | Tvariant tys ->
    List.exists (exists_cpp_type p) tys
  | Tfun (dom, cod) ->
    List.exists (exists_cpp_type p) dom || exists_cpp_type p cod
  | Tconst t | Tshared_ptr t | Tref t | Tptr t | Tnamespace (_, t)
  | Tqualified (t, _) | Tdecay t ->
    exists_cpp_type p t
  | Tapply (t, ts) -> exists_cpp_type p t || List.exists (exists_cpp_type p) ts
  | Tdecltype _ (* wraps a [CPPraw]: no sub-types *)
  | Ttyctor _ | Tvar _ | Tinstance _ | Tpromoted _ | Tvoid | Tunresolved
  | Tany | Topaque | Tauto ->
    false

(** Whether [ty] mentions a [std::shared_ptr] anywhere, however deeply — as the
    element of a container, a function's argument or result, or the type
    itself. *)
let contains_shared_ptr ty =
  exists_cpp_type (function Tshared_ptr _ -> true | _ -> false) ty

(* {1 The reversal convention}

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
let to_reversed (l : 'a revd) : 'a list = l.rev

(** A list that is already in reverse order, admitted as one.  Use where the
    reversal is genuinely already done -- threading a sublist of an existing
    call's arguments, say -- and {!mk_call} or {!mk_lambda} everywhere else. *)
let of_reversed (l : 'a list) : 'a revd = {rev = l}

(** The signature of a call nothing is known about. *)
let call_opaque = {cs_yields = Ropaque; cs_params = Punknown}

(** [call_sig ?yields ?params ()] is what a builder knows about a call.
    [params] is recorded only when it is positionally aligned with the
    arguments; a length mismatch is no knowledge at all, so it is dropped
    rather than stored misaligned. *)
let call_sig ?yields ?params ~nargs () =
  { cs_yields = (match yields with Some t -> Ryields t | None -> Ropaque);
    cs_params =
      ( match params with
      | Some ts when List.length ts = nargs -> Ptypes ts
      | _ -> Punknown ) }

(** [mk_call ?yields ?params fn args] is a call of [fn] on [args] given in
    {e source} order.  [yields] is the call's result type and [params] the
    callee's parameter types, where the builder knows them; omitting either
    is a claim -- that the callee has no Crane-level type there -- and not a
    shrug. *)
let mk_call ?yields ?params fn args =
  let res = call_sig ?yields ?params ~nargs:(List.length args) () in
  match (fn, args) with
  (* [fn] never returns, so the call never happens: it is that same
     abort, which already carries the type the call would have had. *)
  | CPPabort _, [] -> fn
  | _ -> CPPfun_call (res, fn, {rev = List.rev args})

(** [mk_apply fn args] applies [fn] to [args], given in {e source} order.

    Applying no arguments is nothing to apply, so it is [fn] itself -- unlike
    {!mk_call}, where the empty list is a nullary call [fn()].  Reach for this
    where the arguments are whatever a call site had left over. *)
let mk_apply ?yields ?params fn args =
  match args with [] -> fn | _ -> mk_call ?yields ?params fn args

(** [mk_lambda params ret body ~by_value] is a lambda whose [params] are given
    in {e source} order.  [by_value] selects a [\[=\]] capture over [\[&\]].

    A trailing return type is a by-value return, so a top-level [const] on it
    says nothing and [-Wignored-qualifiers] rejects it.  Callers routinely
    reach for the type of whatever the lambda stands in for -- a [const]
    initialiser's own type, say -- so the qualifier is dropped here rather
    than at each of them.  A [const] under a reference is a different claim
    and is left alone.

    A nullary lambda whose body only throws produces no value, so it is
    {!CPPabort} instead: the same never-returning expression, and the one
    spelling of it.  An un-annotated such lambda would otherwise deduce
    [void] and could not stand where a value is expected; [Tany] is what an
    erased slot asks for, and is the only thing left to say when the caller
    named no type. *)
let lambda params ret body ~by_value =
  { cl_params = {rev = List.rev params};
    cl_ret = (match ret with Some (Tconst t) -> Some t | r -> r);
    cl_body = body;
    cl_by_value = by_value }

let mk_lambda params ret body ~by_value =
  let l = lambda params ret body ~by_value in
  match (params, body) with
  | [], [Sthrow msg] ->
    CPPabort (msg, match l.cl_ret with Some t -> t | None -> Tany)
  | _ -> CPPlambda l

(** [mk_iife ret body] evaluates [body] in place: a nullary lambda, invoked
    immediately, capturing by reference.

    A body that does nothing but throw yields no value, so the lambda would
    deduce [void] and could not stand where a value is expected; it reduces to
    {!CPPabort}, which carries [ret] as the type it yields. *)
let mk_iife ret body = mk_call (mk_lambda [] ret body ~by_value:false) []

(** The arguments of a {!CPPfun_call}, in source order. *)
let call_args (args : 'a revd) = List.rev args.rev

(** [map_args f args] rewrites each of a call's arguments with [f], keeping
    them in the order they are stored.  For the many rewriters that descend
    through a call without caring what order its arguments are in. *)
let map_args f (args : cpp_expr revd) = {rev = List.map f args.rev}

(** The parameters of a {!CPPlambda}, in source order. *)
let lambda_params (params : 'a revd) = List.rev params.rev

(** [map_lambda fs ft l] maps [ft] over the parameter and return types of [l]
    and [fs] over its body.  A lambda has no immediate sub-expression of its
    own, so there is no expression function to take. *)
let map_lambda fs ft l =
  { l with
    cl_params =
      of_reversed
        (List.map (fun (ty, id) -> (ft ty, id)) (to_reversed l.cl_params));
    cl_ret = Option.map ft l.cl_ret;
    cl_body = List.map fs l.cl_body }

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
  | CPPfun_call (res, f, args) ->
    let res =
      { cs_yields =
          (match res.cs_yields with Ryields t -> Ryields (ft t) | Ropaque -> Ropaque);
        cs_params =
          (match res.cs_params with
          | Ptypes ts -> Ptypes (List.map ft ts)
          | Punknown -> Punknown) }
    in
    CPPfun_call (res, fe f, {rev = List.map fe args.rev})
  | CPPconverting_ctor (ty, args) -> CPPconverting_ctor (ft ty, List.map fe args)
  | CPPbox (ty, e') -> CPPbox (ft ty, fe e')
  | CPPderef e' -> CPPderef (fe e')
  | CPPmove e' -> CPPmove (fe e')
  | CPPforward (ty, e') -> CPPforward (ft ty, fe e')
  | CPPlambda l -> CPPlambda (map_lambda fs ft l)
  | CPPalloc (k, ty) -> CPPalloc (k, ft ty)
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
  | CPPconcept_app (c, subj, tys) -> CPPconcept_app (c, subj, List.map ft tys)
  | CPPnew (ty, args) -> CPPnew (ft ty, List.map fe args)
  | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ft ty, fe e')
  | CPPthis -> e
  | CPPshared_from_this ty -> CPPshared_from_this (ft ty)
  | CPPaccess (a, e', id) -> CPPaccess (a, fe e', id)
  | CPPaccess_call (a, obj, id, args) ->
    CPPaccess_call (a, fe obj, id, List.map fe args)
  | CPPscope (e', id, tys) -> CPPscope (fe e', id, List.map ft tys)
  | CPPqualified_t (ty, id) -> CPPqualified_t (ft ty, id)
  | CPPconvertible_to ty -> CPPconvertible_to (ft ty)
  | CPPabort (msg, ty) -> CPPabort (msg, ft ty)
  | CPPenum_val _ -> e
  | CPPnullptr -> e
  | CPPbraced args -> CPPbraced (List.map fe args)
  | CPPstd_get (ty, e_opt) -> CPPstd_get (ft ty, Option.map fe e_opt)
  | CPPstd_holds_alternative ty -> CPPstd_holds_alternative (ft ty)
  | CPPdeclval ty -> CPPdeclval (ft ty)
  | CPPis_same (t1, t2) -> CPPis_same (ft t1, ft t2)
  | CPPtype_name ty -> CPPtype_name (ft ty)
  | CPPlit (ty, s) -> CPPlit (ft ty, s)
  | CPPraw _ | CPPrt _ -> e
  | CPPbinop (op, e1, e2) -> CPPbinop (op, fe e1, fe e2)
  | CPPcond (c, t, f) -> CPPcond (fe c, fe t, fe f)
  | CPPbool _ -> e
  | CPPint _ -> e
  | CPPunop (op, e') -> CPPunop (op, fe e')
  | CPPany_cast (ty, e') -> CPPany_cast (ft ty, fe e')
  | CPPany_cast_tolerant (ty, e') -> CPPany_cast_tolerant (ft ty, fe e')
  | CPPerase_fn (ty, e') -> CPPerase_fn (Option.map ft ty, fe e')
  | CPPfn_value e' -> CPPfn_value (fe e')
  | CPPcontainer_cast (ty, e', sb) -> CPPcontainer_cast (ft ty, fe e', sb)
  | CPPstd_get_if (ty, e') -> CPPstd_get_if (ft ty, fe e')

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
  | Sasgn (id, tgt, e) ->
    let tgt = match tgt with Declare ty -> Declare (ft ty) | Existing -> tgt in
    Sasgn (id, tgt, fe e)
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
  | Sif_constexpr (cond, then_br, else_br) ->
    Sif_constexpr (fe cond, List.map fs then_br, List.map fs else_br)
  | Sif (cond, then_br, else_br) ->
    Sif (fe cond, List.map fs then_br, List.map fs else_br)
  | Sif_decl (id, ty, init, then_br, else_br) ->
    Sif_decl (id, ft ty, fe init, List.map fs then_br, List.map fs else_br)
  | Sraw _ | Scomment _ -> s
  | Sstruct_def (id, fields) ->
    Sstruct_def (id, List.map (fun (fid, ty) -> (fid, ft ty)) fields)
  | Susing (id, ty) -> Susing (id, ft ty)
  | Sdecl_init (id, ty) -> Sdecl_init (id, ft ty)
  | Sassign_expr (lhs, e) -> Sassign_expr (fe lhs, fe e)
  | Sfor_range (id, e, body) -> Sfor_range (id, fe e, List.map fs body)
  | Swhile (cond, body) -> Swhile (fe cond, List.map fs body)
  | Sblock stmts -> Sblock (List.map fs stmts)
  | Scontinue -> s
  | Sbreak -> s
  | Sblock_custom (r, tmpl, id, ty, args, tys) ->
    Sblock_custom (r, tmpl, id, ft ty, List.map fe args, List.map ft tys)
  | Smatch (scrut, branches, default) ->
    Smatch
      ( { scrut with sc_expr = fe scrut.sc_expr },
        List.map
          (fun br ->
            { smb_ctor_type = ft br.smb_ctor_type;
              smb_var = br.smb_var;
              smb_field_bindings =
                List.map (fun (id, ty, u) -> (id, ft ty, u)) br.smb_field_bindings;
              smb_extra_conds = List.map fe br.smb_extra_conds;
              smb_body = List.map fs br.smb_body })
          branches,
        Option.map (List.map fs) default )

(** Iterate over the immediate children of a [cpp_expr], calling [on_expr]
    for child expressions and [on_stmts] for child statement lists.  Does
    not recurse — the caller controls recursion depth.  Covers every
    constructor in {!cpp_expr}. *)
let iter_expr_children ~on_expr ~on_stmts (e : cpp_expr) : unit =
  match e with
  | CPPvar _ | CPPglob _ | CPPalloc _
  | CPPstring _ | CPPuint _ | CPPfloat _ | CPPconvertible_to _
  | CPPabort _ | CPPenum_val _ | CPPnullptr | CPPstd_holds_alternative _
  | CPPis_same _
  | CPPdeclval _ | CPPtype_name _ | CPPqualified_t _ | CPPlit _
   |CPPraw _ | CPPrt _
  | CPPbool _ | CPPint _
  | CPPconcept_app _ | CPPthis | CPPshared_from_this _ -> ()
  | CPPfun_call (_, f, args) -> on_expr f; List.iter on_expr args.rev
  | CPPconverting_ctor (_, args) -> List.iter on_expr args
  | CPPbox (_, e') -> on_expr e'
  | CPPnamespace (_, e') | CPPderef e' | CPPmove e' | CPPforward (_, e')
  | CPPget (e', _) | CPPget' (e', _) | CPPaccess (_, e', _)
  | CPPscope (e', _, _)
  | CPPshared_ptr_ctor (_, e')
  | CPPany_cast (_, e') | CPPany_cast_tolerant (_, e')
  | CPPcontainer_cast (_, e', _) | CPPerase_fn (_, e') | CPPfn_value e'
  | CPPunop (_, e') | CPPstd_get_if (_, e') ->
    on_expr e'
  | CPPlambda l -> on_stmts l.cl_body
  | CPPstructmk (_, _, es) | CPPstruct (_, _, es)
  | CPPstruct_id (_, _, es) | CPPnew (_, es) ->
    List.iter on_expr es
  | CPPparray (arr, e') -> Array.iter on_expr arr; on_expr e'
  | CPPaccess_call (_, obj, _, args) -> on_expr obj; List.iter on_expr args
  | CPPrequires (_, constraints, _) ->
    List.iter (fun (e', _) -> on_expr e') constraints
  | CPPbinop (_, l, r) -> on_expr l; on_expr r
  | CPPcond (c, t, f) -> on_expr c; on_expr t; on_expr f
  | CPPbraced args -> List.iter on_expr args
  | CPPstd_get (_, e_opt) -> Option.iter on_expr e_opt

(** Iterate over the immediate children of a [cpp_stmt], calling [on_expr]
    for child expressions and [on_stmts] for child statement lists.  Does
    not recurse — the caller controls recursion depth.  Covers every
    constructor in {!cpp_stmt}. *)
let iter_stmt_children ~on_expr ~on_stmts (s : cpp_stmt) : unit =
  match s with
  | Sreturn (Some e) | Sexpr e -> on_expr e
  | Sreturn None | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Scomment _
  | Sstruct_def _ | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> ()
  | Sasgn (_, _, e) -> on_expr e
  | Sif_constexpr (cond, then_br, else_br) ->
    on_expr cond; on_stmts then_br; on_stmts else_br
  | Sif (cond, then_br, else_br) ->
    on_expr cond; on_stmts then_br; on_stmts else_br
  | Sif_decl (_, _, init, then_br, else_br) ->
    on_expr init; on_stmts then_br; on_stmts else_br
  | Sswitch (scrut, _, branches, default) ->
    on_expr scrut;
    List.iter (fun (_, stmts) -> on_stmts stmts) branches;
    Option.iter on_stmts default
  | Scustom_case (_, scrut, _, branches, _) ->
    on_expr scrut;
    List.iter (fun (_, _, stmts) -> on_stmts stmts) branches
  | Sassign_expr (lhs, e) -> on_expr lhs; on_expr e
  | Sfor_range (_, e, body) -> on_expr e; on_stmts body
  | Swhile (cond, body) -> on_expr cond; on_stmts body
  | Sblock stmts -> on_stmts stmts
  | Sblock_custom (_, _, _, _, args, _) -> List.iter on_expr args
  | Smatch (scrut, branches, default) ->
    on_expr scrut.sc_expr;
    List.iter (fun br ->
      List.iter on_expr br.smb_extra_conds;
      on_stmts br.smb_body) branches;
    Option.iter on_stmts default

(** Fold over immediate children of a [cpp_expr].  Mirrors
    {!iter_expr_children} but threads an accumulator: [on_expr] folds over
    child expressions, [on_stmts] over child statement lists (e.g. a
    [CPPlambda] body).  Keeping this in lock-step with {!iter_expr_children}
    matters — a traversal that silently skips lambda bodies would undercount
    variable uses and can make callers (e.g. the move-safety guard in
    [Translation.count_state_uses]) emit an unsound [std::move]. *)
let fold_expr_children ~(on_expr : 'a -> cpp_expr -> 'a)
    ~(on_stmts : 'a -> cpp_stmt list -> 'a) (acc : 'a) (e : cpp_expr) : 'a =
  let fe acc e = on_expr acc e in
  match e with
  | CPPvar _ | CPPglob _ | CPPalloc _
  | CPPstring _ | CPPuint _ | CPPfloat _ | CPPconvertible_to _
  | CPPabort _ | CPPenum_val _ | CPPnullptr | CPPstd_holds_alternative _
  | CPPis_same _
  | CPPdeclval _ | CPPtype_name _ | CPPqualified_t _ | CPPlit _
   |CPPraw _ | CPPrt _
  | CPPbool _ | CPPint _
  | CPPconcept_app _ | CPPthis | CPPshared_from_this _ -> acc
  | CPPlambda l -> on_stmts acc l.cl_body
  | CPPfun_call (_, fn, args) -> List.fold_left fe (fe acc fn) args.rev
  | CPPconverting_ctor (_, args) -> List.fold_left fe acc args
  | CPPbox (_, e') -> fe acc e'
  | CPPnamespace (_, e') | CPPderef e' | CPPmove e' | CPPforward (_, e')
  | CPPget (e', _) | CPPget' (e', _) | CPPaccess (_, e', _)
  | CPPscope (e', _, _)
  | CPPshared_ptr_ctor (_, e')
  | CPPany_cast (_, e') | CPPany_cast_tolerant (_, e')
  | CPPcontainer_cast (_, e', _) | CPPerase_fn (_, e') | CPPfn_value e'
  | CPPunop (_, e') | CPPstd_get_if (_, e') ->
    fe acc e'
  | CPPstructmk (_, _, es) | CPPstruct (_, _, es)
  | CPPstruct_id (_, _, es) | CPPnew (_, es) ->
    List.fold_left fe acc es
  | CPPparray (arr, e') -> fe (Array.fold_left fe acc arr) e'
  | CPPaccess_call (_, obj, _, args) -> List.fold_left fe (fe acc obj) args
  | CPPrequires (_, constraints, _) ->
    List.fold_left (fun a (e', _) -> fe a e') acc constraints
  | CPPbinop (_, l, r) -> fe (fe acc l) r
  | CPPcond (c, t, f) -> fe (fe (fe acc c) t) f
  | CPPbraced args -> List.fold_left fe acc args
  | CPPstd_get (_, e_opt) -> match e_opt with None -> acc | Some e' -> fe acc e'

(** Fold over immediate children of a [cpp_stmt].  [on_expr] folds over
    child expressions; [on_stmts] folds over child statement lists. *)
let fold_stmt_children ~on_expr ~on_stmts (acc : 'a) (s : cpp_stmt) : 'a =
  match s with
  | Sreturn (Some e) | Sexpr e -> on_expr acc e
  | Sreturn None | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Scomment _
  | Sstruct_def _ | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> acc
  | Sasgn (_, _, e) -> on_expr acc e
  | Sif_constexpr (cond, then_br, else_br) ->
    on_stmts (on_stmts (on_expr acc cond) then_br) else_br
  | Sif (cond, then_br, else_br) ->
    on_stmts (on_stmts (on_expr acc cond) then_br) else_br
  | Sif_decl (_, _, init, then_br, else_br) ->
    on_stmts (on_stmts (on_expr acc init) then_br) else_br
  | Sswitch (scrut, _, branches, default) ->
    let acc = on_expr acc scrut in
    let acc = List.fold_left (fun a (_, stmts) -> on_stmts a stmts) acc branches in
    (match default with None -> acc | Some d -> on_stmts acc d)
  | Scustom_case (_, scrut, _, branches, _) ->
    let acc = on_expr acc scrut in
    List.fold_left (fun a (_, _, stmts) -> on_stmts a stmts) acc branches
  | Sassign_expr (lhs, e) -> on_expr (on_expr acc lhs) e
  | Sfor_range (_, e, body) -> on_stmts (on_expr acc e) body
  | Swhile (cond, body) -> on_stmts (on_expr acc cond) body
  | Sblock stmts -> on_stmts acc stmts
  | Sblock_custom (_, _, _, _, args, _) -> List.fold_left on_expr acc args
  | Smatch (scrut, branches, default) ->
    let acc = on_expr acc scrut.sc_expr in
    let acc =
      List.fold_left (fun a br ->
        let a = List.fold_left on_expr a br.smb_extra_conds in
        on_stmts a br.smb_body) acc branches
    in
    (match default with None -> acc | Some d -> on_stmts acc d)

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
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
  | Dconcept of
      GlobRef.t
      * cpp_expr (* template params are provided by an outer Dtemplate *)
  | Dstatic_assert of cpp_expr * string option
  | Dusing of GlobRef.t * cpp_type
      (* [using name = ty;] -- a second spelling of an existing type *)
  | Denum of {
      de_ref : GlobRef.t;
      de_ctors : Id.t list;
      de_ctor_rocq_names : string list;
      de_tparams : (template_type * Id.t) list;
    }

(** [map_field fe fs ft f] applies [fe] to sub-expressions, [fs] to
    sub-statements and [ft] to sub-types of a visibility-annotated field,
    performing one level of structural descent.  Nested structs recurse, so
    that a caller need only supply the three leaf functions. *)
let rec map_field
    (fe : cpp_expr -> cpp_expr)
    (fs : cpp_stmt -> cpp_stmt)
    (ft : cpp_type -> cpp_type)
    ((f, vis, tag) : cpp_field * cpp_visibility * section_tag) :
    cpp_field * cpp_visibility * section_tag =
  let params ps = List.map (fun (id, ty) -> (id, ft ty)) ps in
  let f' =
    match f with
    | Fvar (id, ty) -> Fvar (id, ft ty)
    | Fvar' (r, ty) -> Fvar' (r, ft ty)
    | Fmethod m ->
      Fmethod
        { m with
          mf_ret_type = ft m.mf_ret_type;
          mf_params = params m.mf_params;
          mf_body = List.map fs m.mf_body }
    | Fconstructor (ps, inits, expl, noexc) ->
      Fconstructor
        (params ps, List.map (fun (id, e) -> (id, fe e)) inits, expl, noexc)
    | Fdestructor body -> Fdestructor (List.map fs body)
    | Fnested_struct (id, fields) ->
      Fnested_struct (id, List.map (map_field fe fs ft) fields)
    | Fnested_using (tps, id, ty) -> Fnested_using (tps, id, ft ty)
    | Ftemplate_ctor (tps, expl, ps, body) ->
      Ftemplate_ctor (tps, expl, params ps, List.map fs body)
    | Fdeleted_ctor | Fdefaulted_special_members -> f
  in
  (f', vis, tag)

(** [map_decl fe fs ft d] applies [fe] to sub-expressions, [fs] to
    sub-statements and [ft] to sub-types of a declaration.  Nested
    declarations ({!Dtemplate}, {!Dnspace}) recurse. *)
let rec map_decl
    (fe : cpp_expr -> cpp_expr)
    (fs : cpp_stmt -> cpp_stmt)
    (ft : cpp_type -> cpp_type)
    (d : cpp_decl) : cpp_decl =
  match d with
  | Dtemplate (tps, constr, inner) ->
    Dtemplate (tps, Option.map fe constr, map_decl fe fs ft inner)
  | Dnspace (r, decls) -> Dnspace (r, List.map (map_decl fe fs ft) decls)
  | Dfundef (names, ret, ps, body, no_pure) ->
    Dfundef
      ( List.map (fun (r, tys) -> (r, List.map ft tys)) names,
        ft ret,
        List.map (fun (id, ty) -> (id, ft ty)) ps,
        List.map fs body,
        no_pure )
  | Dfundecl (names, ret, ps, no_pure) ->
    Dfundecl
      ( List.map (fun (r, tys) -> (r, List.map ft tys)) names,
        ft ret,
        List.map (fun (id, ty) -> (id, ft ty)) ps,
        no_pure )
  | Dstruct s ->
    Dstruct
      { s with
        ds_fields = List.map (map_field fe fs ft) s.ds_fields;
        ds_constraint = Option.map fe s.ds_constraint }
  | Dasgn (r, ty, e) -> Dasgn (r, ft ty, fe e)
  | Dconcept (r, e) -> Dconcept (r, fe e)
  | Dstatic_assert (e, msg) -> Dstatic_assert (fe e, msg)
  | Dusing (r, ty) -> Dusing (r, ft ty)
  | Denum _ -> d
