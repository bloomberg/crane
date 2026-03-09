(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Target language for extraction: a core C++ called MiniCpp.

   Crane's extraction pipeline has two intermediate representations:

     Rocq CIC  --[extraction.ml]-->  MiniML  --[translation.ml]-->  MiniCpp  --[cpp.ml]-->  C++

   MiniML (miniml.ml) handles type erasure, signature computation, and
   ML-level optimizations on a language-agnostic functional AST.  MiniCpp
   (this file) captures C++-specific idioms: shared_ptr/unique_ptr memory
   management, std::variant, templates, concepts, namespaces, structs
   with visibility, move semantics, enum classes, and constructors.

   See minicpp.ml for a detailed explanation of why both representations
   are needed and cannot be merged. *)

open Names

(*s Pre-resolved C++ name.
   Computed during translation so the pretty-printer doesn't need
   name-resolution logic. *)
type cpp_name = {
  cn_base : string;               (* e.g., "add", "list", "Nat" *)
  cn_qualified : string option;    (* Some "Nat::" for wrapper-qualified names *)
  cn_needs_typename : bool;        (* true if dependent type in template context *)
}

(*s Inductive classification — determined once during translation. *)
type cpp_ind_kind =
  | IK_Standard                             (* std::variant sum type *)
  | IK_Enum                                 (* enum class *)
  | IK_Record of GlobRef.t option list      (* struct with named fields *)
  | IK_Eponymous of GlobRef.t option list   (* record merged into module *)
  | IK_TypeClass of GlobRef.t option list   (* C++ concept *)

(*s Custom extraction info — resolved once during translation. *)
type custom_info = {
  ci_inline : string option;   (* Some code if to_inline, None otherwise *)
  ci_is_custom : bool;
}

(*s Visibility for struct members. *)
type cpp_visibility = VPublic | VPrivate

type cpp_tymod =
  | TMconst
  | TMstatic
  | TMextern


type cpp_type =
  | Tvar of int * Id.t option
  | Tid of Id.t * cpp_type list  (* Simple Id-based type, for local names like nested structs *)
  | Tglob of GlobRef.t * cpp_type list * cpp_expr list
  | Tfun of cpp_type list * cpp_type
  | Tmod of cpp_tymod * cpp_type
  | Tnamespace of GlobRef.t * cpp_type
  | Tqualified of cpp_type * Id.t  (* typename Base<T>::nested - for nested struct access *)
  | Tref of cpp_type
  | Tvariant of cpp_type list
  | Tshared_ptr of cpp_type
  | Tunique_ptr of cpp_type
  | Tvoid
  | Ttodo
  | Tunknown
  | Tany  (* std::any - for type-erased storage of existential types *)

and cpp_meta = { id : int; mutable contents : cpp_type option }

and cpp_stmt =
  | Sreturn of cpp_expr option
  | Sdecl of Id.t * cpp_type
  | Sasgn of Id.t * cpp_type option * cpp_expr
  | Sexpr of cpp_expr
  | Scustom_case of cpp_type * cpp_expr * cpp_type list * ((Id.t * cpp_type) list * cpp_type * cpp_stmt list) list * string
  | Sthrow of string  (* throw statement for unreachable/absurd cases *)
  | Sswitch of cpp_expr * GlobRef.t * (Id.t * cpp_stmt list) list  (* switch on enum: scrutinee, enum type, branches *)
  | Sassert of string * string option  (* runtime assert: C++ expression string, optional Rocq predicate comment *)
  | Sif of cpp_expr * cpp_stmt list * cpp_stmt list
      (* if-else: condition, then-branch, else-branch.
         Used for reuse optimization's use_count() check. *)
  | Sraw of string
      (* Raw C++ code, printed verbatim.
         Used for low-level operations in reuse optimization. *)
  | Sassign_field of cpp_expr * Id.t * cpp_expr
      (* Field assignment: obj.field = expr.
         Used for in-place mutation during memory reuse. *)

and cpp_expr =
  | CPPvar of Id.t
  | CPPglob of GlobRef.t * cpp_type list * custom_info option
  | CPPnamespace of GlobRef.t * cpp_expr
  | CPPfun_call of cpp_expr * cpp_expr list
  | CPPderef of cpp_expr
  | CPPmove of cpp_expr
  | CPPforward of cpp_type * cpp_expr
  | CPPlambda of (cpp_type * Id.t option) list * cpp_type option * cpp_stmt list * bool (* capture_by_value *)
  | CPPvisit
  | CPPmk_shared of cpp_type
  | CPPoverloaded of cpp_expr list (* cpp_expressions in list should only be lambdas. TODO: enforce in the AST? split up to a funcall *)
  | CPPstructmk of GlobRef.t * cpp_type list * cpp_expr list
  | CPPstruct of GlobRef.t * cpp_type list *  cpp_expr list (* record struct construction via namespace *)
  | CPPstruct_id of Id.t * cpp_type list * cpp_expr list (* Local struct init with Id, e.g., Leaf{} *)
  | CPPget of cpp_expr * Id.t (* access from a struct (or class) *)
  | CPPget' of cpp_expr * GlobRef.t (* access from a struct (or class) *)
  | CPPstring of Pstring.t
  | CPPuint   of Uint63.t
  | CPPfloat  of Float64.t
  | CPPparray of cpp_expr array * cpp_expr
  | CPPrequires of (cpp_type * Id.t) list * (cpp_expr * cpp_constraint) list * cpp_type list
  (* requires (params) { typename type_reqs; { expr } -> constraint; } *)
  | CPPnew of cpp_type * cpp_expr list  (* new Type(args) or new Type{args} *)
  | CPPshared_ptr_ctor of cpp_type * cpp_expr  (* std::shared_ptr<T>(expr) *)
  | CPPunique_ptr_ctor of cpp_type * cpp_expr  (* std::unique_ptr<T>(expr) *)
  | CPPmk_unique of cpp_type                   (* std::make_unique<T> *)
  | CPPthis  (* this pointer in methods *)
  | CPPmember of cpp_expr * Id.t  (* expr.member - for accessing v_ etc *)
  | CPParrow of cpp_expr * Id.t   (* expr->member - for ptr->v_ access *)
  | CPPmethod_call of cpp_expr * Id.t * cpp_expr list  (* obj->method(args) *)
  | CPPqualified of cpp_expr * Id.t  (* expr::id - for qualified name access like Type::ctor *)
  | CPPconvertible_to of cpp_type  (* std::convertible_to<T> constraint *)
  | CPPabort of string  (* unreachable code / absurd case - calls std::abort() *)
  | CPPenum_val of GlobRef.t * Id.t  (* enum class value: EnumType::Constructor *)
  | CPPraw of string
      (* Raw C++ expression, printed verbatim.
         Used for low-level operations (e.g., literal "1" for use_count check). *)
  | CPPbinop of string * cpp_expr * cpp_expr
      (* Binary operator: operator string, lhs, rhs.
         Used for conditions in reuse optimization (&&, ==). *)

and cpp_constraint = cpp_expr

and template_type =
  | TTtypename
  | TTtypename_default of cpp_type  (* typename T = default_type *)
  | TTfun of (cpp_type list * cpp_type)
  | TTconcept of GlobRef.t  (* e.g., 'Eq T' *)

(* TODO: maybe switch all Id.t to GlobRef.t *)
and cpp_field =
  | Fvar of Id.t * cpp_type
  | Fvar' of GlobRef.t * cpp_type
  | Ffundef of Id.t * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
  | Ffundecl of Id.t * cpp_type * (Id.t * cpp_type) list
  | Fmethod of method_field
  (* Private constructor: params, initializer list (as stmts for v_(x) style) *)
  | Fconstructor of (Id.t * cpp_type) list * (Id.t * cpp_expr) list * bool (* bool = explicit *)
  (* Nested struct with its own visibility-annotated fields *)
  | Fnested_struct of Id.t * (cpp_field * cpp_visibility) list
  (* Nested using declaration *)
  | Fnested_using of Id.t * cpp_type
  (* Deleted default constructor: ctor() = delete *)
  | Fdeleted_ctor

and method_field = {
  mf_name : Id.t;
  mf_tparams : (template_type * Id.t) list;
  mf_ret_type : cpp_type;
  mf_params : (Id.t * cpp_type) list;
  mf_body : cpp_stmt list;
  mf_is_const : bool;
  mf_is_static : bool;
}

(* C++ type schema.
   The integer is the number of variables in the schema. *)

type cpp_schema = int * cpp_type

val ind_ty_ptr : GlobRef.t -> cpp_type list -> cpp_type
val ind_ty_uptr : GlobRef.t -> cpp_type list -> cpp_type

type cpp_decl =
  | Dtemplate of (template_type * Id.t) list  * cpp_constraint option * cpp_decl
  | Dnspace of GlobRef.t option * cpp_decl list
  | Dfundef of (GlobRef.t * cpp_type list) list * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
  | Dfundecl of (GlobRef.t * cpp_type list) list * cpp_type * (Id.t option * cpp_type) list
  | Dstruct of {
      ds_ref : GlobRef.t;
      ds_fields : (cpp_field * cpp_visibility) list;
      ds_tparams : (template_type * Id.t) list;      (* [] for non-template structs *)
      ds_constraint : cpp_constraint option;          (* template constraint, if any *)
    }
  | Dstruct_decl of GlobRef.t
  | Dusing of GlobRef.t * cpp_type
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
  | Ddecl of GlobRef.t * cpp_type
  | Dconcept of GlobRef.t * cpp_expr (* template params are provided by an outer Dtemplate *)
  | Dstatic_assert of cpp_expr * string option
  | Denum of {
      de_ref : GlobRef.t;
      de_ctors : Id.t list;
      de_tparams : (template_type * Id.t) list;
    }
