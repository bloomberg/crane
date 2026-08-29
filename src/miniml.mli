(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Target language for extraction: a core ML called MiniML.

    MiniML is the language-agnostic functional intermediate representation at
    the heart of the extractor.  The pipeline is

    {[ Rocq CIC --[extraction.ml]--> MiniML --[translation.ml]--> MiniCpp
       --[cpp.ml]--> C++ ]}

    Extraction from Rocq's CIC first erases everything with no computational
    content — types, logical ([Prop]) subterms, and user-declared implicit
    arguments — recording what was removed in a {!signature}.  The surviving
    computation is expressed in this AST: {!ml_type} for type expressions,
    {!ml_ast} for terms, {!ml_ind} for inductive declarations, and
    {!ml_decl} / {!ml_specif} for whole definitions and module components.
    ML-level optimisations (inlining, dead-code elimination, currying fixes)
    run over these trees before {!Translation} lowers them to the C++-shaped
    {!Minicpp} IR.

    This module is inherited largely unchanged from Rocq's own extraction
    plugin; Crane extends it (notably {!ml_ind_packet}'s [ip_consarg_names])
    to carry the extra information the C++ backend needs. *)

open Names

(* The [signature] type is used to know how many arguments a CIC object expects,
   and what these arguments will become in the ML object. *)

(** Why a CIC argument or subterm carries no computational content and is
    therefore erased during extraction. [Ktype] marks a type argument, [Kprop]
    a logical ([Prop]) part, and [Kimplicit (r, n)] the [n]-th argument of the
    constant or constructor [r] that the user declared implicit. *)
type kill_reason =
  | Ktype
  | Kprop
  | Kimplicit of GlobRef.t * int  (** n-th arg of a cst or construct *)

(** Fate of a single CIC argument once extraction has run: [Keep] it in the ML
    object, or [Kill] it with the recorded {!kill_reason}. *)
type sign =
  | Keep
  | Kill of kill_reason

(** Per-argument keep/kill decisions for a CIC object, one {!sign} per argument.
    Convention: the outermost lambda/product gives the head of the list, so the
    signature is read left-to-right in source order. *)
type signature = sign list

(** An ML binder name. [Id] wraps a real Rocq identifier; [Dummy] names a
    binder for an erased/unused argument (no meaningful name survived); [Tmp] is
    a freshly generated temporary introduced by ML-level transformations. *)
type ml_ident =
  | Dummy
  | Id of Id.t
  | Tmp of Id.t

(** {2 ML type expressions} *)

(** An erased ML type expression, the residue of a CIC type after logical and
    type-only content is removed. Key constructors: [Tarr] is a (non-dependent)
    function arrow; [Tglob (r, tys, args)] applies the named inductive/type
    constant [r] to type arguments [tys] (Crane additionally carries value
    [args] for indexed/dependent positions); [Tvar]/[Tvar'] are De Bruijn type
    variables, [Tvar'] being an alias generation used to avoid capture clashes;
    [Tmeta] is a mutable unification variable used only during ML type
    reconstruction; [Tdummy] stands for a type slot that was erased (its
    {!kill_reason} records why); [Tunknown] marks a type inference gave up on;
    [Taxiom] a type left abstract by an axiom; and [Tstring] the primitive
    string type. *)
type ml_type =
  | Tarr of ml_type * ml_type
  | Tglob of GlobRef.t * ml_type list * ml_ast list
  | Tvar of int
  | Tvar' of int  (** same as Tvar, used to avoid clash *)
  | Tapp of int * ml_type list
      (** A type variable of arrow kind applied to arguments: the [M A] of
          [mret : forall A, A -> M A], where [M : Type -> Type] is a
          higher-kinded class parameter.  The head is a [Tvar] index. *)
  | Tmeta of ml_meta  (** used during ML type reconstruction *)
  | Tdummy of kill_reason
  | Tunknown
  | Taxiom
  | Tstring

(** A mutable type metavariable used while reconstructing ML types: [id]
    identifies it and [contents] is filled in with the resolved type once
    unification succeeds (staying [None] until then). *)
and ml_meta = {
  id : int;
  mutable contents : ml_type option;
}

(** {2 ML inductive types} *)

(** How an inductive type should be treated by the backend. [Standard] is an
    ordinary (finite) inductive; [Coinductive] a lazily-unfolded one; [Record]
    a single-constructor inductive presented with named projections (the list
    gives each field's projection reference, [None] for an anonymous field);
    and [TypeClass] a record standing for a Rocq type class, whose fields are
    its methods. *)
and inductive_kind =
  | Coinductive
  | Standard
  | Record of GlobRef.t option list  (** None for anonymous field *)
  | TypeClass of GlobRef.t option list  (** Type class methods *)

(** The miniml counterpart of a single kernel [one_inductive_body], i.e. one of
    the (mutually) defined inductive types. When [ip_logical] is [true] the type
    has no computational content and the remaining fields are unused; otherwise
    [ip_typename] is the type's name, [ip_consnames] the constructor names,
    [ip_sign] the {!signature} for the inductive's own arguments, [ip_vars] the
    names of the type variables surviving into ML, and [ip_types] the ML
    argument types of each constructor (indexed by constructor ordinal).

    Crane adds [ip_consarg_names]: for each constructor (indexed the same way),
    the list of its argument binder names extracted from the kernel
    ([mind_user_lc]), [Some id] for a named binder and [None] for an anonymous
    one. This lets C++ generation emit meaningful field names (e.g. [d_left],
    [d_value]) instead of positional [d_a0], [d_a1]. See [miniml.ml] for the
    worked example. *)
and ml_ind_packet = {
  ip_typename : Id.t;
  ip_consnames : Id.t array;
  ip_logical : bool;
  ip_sign : signature;
  mutable ip_vars : Id.t list;
  ip_types : ml_type list array;
  ip_consarg_names : Id.t option list array;
}

(** How an inductive relates to another already-extracted one, used to share
    definitions. [NoEquiv] means it is emitted on its own; [Equiv kn] redirects
    it to the kernel name [kn] of an equivalent inductive; [RenEquiv s]
    redirects to an inductive living in the module renamed [s]. *)
and equiv =
  | NoEquiv
  | Equiv of KerName.t
  | RenEquiv of string

(** A whole (possibly mutual) inductive definition: [ind_kind] its
    classification, [ind_nparams] the number of uniform parameters,
    [ind_packets] one {!ml_ind_packet} per mutually-defined body, and
    [ind_equiv] any sharing/redirection information. *)
and ml_ind = {
  ind_kind : inductive_kind;
  ind_nparams : int;
  ind_packets : ml_ind_packet array;
  ind_equiv : equiv;
}

(** {2 ML terms} *)

(** A single {!MLcase} branch, as [(binders, ret_type, pattern, body)].
    [binders] are the variables bound by [pattern] paired with their ML types,
    [ret_type] is the branch's result type, and [body] the term run when
    [pattern] matches. *)
and ml_branch = (ml_ident * ml_type) list * ml_type * ml_pattern * ml_ast

(** An erased ML term — the computational residue of a CIC term. Key
    constructors: [MLrel] a De Bruijn-indexed local variable; [MLapp] an
    application of a head to a list of arguments; [MLlam] a lambda (binder, its
    type, body); [MLletin] a let-binding; [MLglob] a reference to a global
    constant with its type arguments; [MLcons] a constructor application (its
    {!ml_type} records the constructed type); [MLtuple] an anonymous tuple;
    [MLcase] a pattern match (matched-head type, scrutinee, branches); [MLfix]
    a block of mutually recursive fixpoints (index of the selected component,
    the name/type of each, their bodies, and a flag distinguishing cofixpoints);
    [MLexn] a runtime error raised for an unrealisable term; [MLdummy] the value
    of an erased/logical slot; [MLaxiom] a value left abstract by an axiom;
    [MLmagic] an unsafe coercion bridging type gaps opened by erasure; the
    primitive literals [MLuint], [MLfloat] and [MLstring]; and [MLparray] a
    persistent-array literal (element array plus default value).

    Typing note: [MLcons] and [MLcase] deliberately carry an {!ml_type} — the
    type of the applied constructor, or of the matched head — so that later
    optimisations remain type-safe. [MLtuple] and the extension of [MLcase] to
    general patterns come from P.N. Tollitte's Relation Extraction plugin;
    [MLtuple] and deep patterns are unused by the main extraction. *)
and ml_ast =
  | MLrel of int
  | MLapp of ml_ast * ml_ast list
  | MLlam of ml_ident * ml_type * ml_ast
  | MLletin of ml_ident * ml_type * ml_ast * ml_ast
  | MLglob of GlobRef.t * ml_type list
  | MLcons of ml_type * GlobRef.t * ml_ast list
  | MLtuple of ml_ast list
  | MLcase of ml_type * ml_ast * ml_branch array
  | MLfix of int * (Id.t * ml_type) array * ml_ast array * bool  (** is_cofix *)
  | MLexn of string
  | MLdummy of kill_reason
  | MLaxiom of string
  | MLmagic of ml_ast
  | MLuint of Uint63.t
  | MLfloat of Float64.t
  | MLstring of Pstring.t
  | MLparray of ml_ast array * ml_ast

(** A match pattern. [Pcons (r, ps)] matches constructor [r] with sub-patterns
    [ps]; [Ptuple] matches a tuple; [Prel] refers to a bound branch variable by
    De Bruijn index; [Pwild] is the wildcard; and [Pusual] is a shorthand for
    the shallow constructor pattern that binds every argument in order. *)
and ml_pattern =
  | Pcons of GlobRef.t * ml_pattern list
  | Ptuple of ml_pattern list
  | Prel of int  (** Cf. the idents in the branch. [Prel 1] is the last one. *)
  | Pwild
  | Pusual of GlobRef.t  (** Shortcut for Pcons (r,[Prel n;...;Prel 1]) **)

(** An ML type schema (prenex polymorphic type): the [int] is the number of
    universally quantified type variables, [ml_type] the body that may mention
    them as [Tvar]s. *)
type ml_schema = int * ml_type

(** {2 ML declarations} *)

(** A concrete, defined top-level ML entity. [Dind] is an inductive definition;
    [Dtype] a type abbreviation (its reference, type-variable names, and body);
    [Dterm] a single term definition (reference, body, type); and [Dfix] a
    block of mutually recursive definitions (parallel arrays of references,
    bodies, and types). *)
type ml_decl =
  | Dind of MutInd.t * ml_ind
  | Dtype of GlobRef.t * Id.t list * ml_type
  | Dterm of GlobRef.t * ml_ast * ml_type
  | Dfix of GlobRef.t array * ml_ast array * ml_type array

(** The specification (interface view) of an ML entity, used when emitting
    signatures. [Sind] specifies an inductive; [Stype] a type name (with an
    optional definition, [None] when abstract); [Sval] a value with its body
    and type. *)
type ml_spec =
  | Sind of MutInd.t * ml_ind
  | Stype of GlobRef.t * Id.t list * ml_type option
  | Sval of GlobRef.t * ml_ast * ml_type

(** A single component of a module signature: a plain {!ml_spec}, a nested
    sub-[Smodule], or a nested [Smodtype] (module-type) declaration. *)
type ml_specif =
  | Spec of ml_spec
  | Smodule of ml_module_type
  | Smodtype of ml_module_type

(** An ML module type. [MTident] names a module type; [MTfunsig] is a functor
    signature (parameter, its type, result type); [MTsig] an explicit signature
    (a list of named {!ml_specif}); and [MTwith] refines a module type with a
    [with] constraint. *)
and ml_module_type =
  | MTident of ModPath.t
  | MTfunsig of MBId.t * ml_module_type * ml_module_type
  | MTsig of ModPath.t * ml_module_sig
  | MTwith of ml_module_type * ml_with_declaration

(** A [with] refinement on a module type, fixing either a type component
    ([ML_With_type]) or a sub-module component ([ML_With_module]) by path. *)
and ml_with_declaration =
  | ML_With_type of Id.t list * Id.t list * ml_type
  | ML_With_module of Id.t list * ModPath.t

(** The body of a module signature: its components paired with their labels. *)
and ml_module_sig = (Label.t * ml_specif) list

(** A single component of a module implementation. [SEdecl] is a definition,
    [SEmodule] a nested module, and [SEmodtype] a nested module-type binding. *)
type ml_structure_elem =
  | SEdecl of ml_decl
  | SEmodule of ml_module
  | SEmodtype of ml_module_type

(** An ML module expression (implementation). [MEident] is a module reference;
    [MEfunctor] a functor (parameter, its type, body); [MEstruct] an explicit
    structure of labelled elements; and [MEapply] a functor application. *)
and ml_module_expr =
  | MEident of ModPath.t
  | MEfunctor of MBId.t * ml_module_type * ml_module_expr
  | MEstruct of ModPath.t * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

(** The body of a module structure: its elements paired with their labels. *)
and ml_module_structure = (Label.t * ml_structure_elem) list

(** A module binding: its implementation [ml_mod_expr] and its type
    [ml_mod_type]. The kernel's [mod_equiv] field is not translated, since
    [mod_equiv = mp] would imply [mod_expr = MEBident mp] (likewise
    [msb_equiv]). *)
and ml_module = {
  ml_mod_expr : ml_module_expr;
  ml_mod_type : ml_module_type;
}

(** A whole extracted program's implementation: the module structure of each
    module path, in dependency order. *)
type ml_structure = (ModPath.t * ml_module_structure) list

(** A whole extracted program's interface: the module signature of each module
    path. *)
type ml_signature = (ModPath.t * ml_module_sig) list

(** Which "unsafe" backend features an extracted program requires, so the
    preamble can emit the corresponding helpers: [mldummy] for {!MLdummy}
    values, [tdummy] for {!Tdummy} types, [tunknown] for {!Tunknown} types, and
    [magic] for {!MLmagic} coercions. *)
type unsafe_needs = {
  mldummy : bool;
  tdummy : bool;
  tunknown : bool;
  magic : bool;
}

(** A backend (target-language) descriptor: the pluggable set of hooks the
    generic extraction driver uses to render {!ml_structure} /
    {!ml_signature} for one concrete output language. It bundles the reserved
    [keywords], source-file conventions ([file_suffix], [file_naming],
    [preamble]) and printers ([pp_struct], [pp_hstruct]), the optional
    interface-file conventions ([sig_suffix], [sig_preamble], [pp_sig]), and
    [pp_decl] for printing one declaration in isolation. *)
type language_descr = {
  keywords : Id.Set.t;
  (* Concerning the source file *)
  file_suffix : string;
  file_naming : ModPath.t -> string;
  (* the second argument is a comment to add to the preamble *)
  preamble : Id.t -> Pp.t option -> ModPath.t list -> unsafe_needs -> Pp.t;
  pp_struct : ml_structure -> Pp.t;
  pp_hstruct : ml_structure -> Pp.t;
  (* Concerning a possible interface file *)
  sig_suffix : string option;
  (* the second argument is a comment to add to the preamble *)
  sig_preamble : Id.t -> Pp.t option -> ModPath.t list -> unsafe_needs -> Pp.t;
  pp_sig : ml_signature -> Pp.t;
  (* for an isolated declaration print *)
  pp_decl : ml_decl -> Pp.t;
}
