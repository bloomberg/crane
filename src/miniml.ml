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

(** Target language for extraction: a core ML called MiniML. *)

open Names

(* A [unit ref] compares and hashes by its contents, which every occurrence
   shares, and is told apart from another only physically. *)
module Occurrence = struct
  type t = unit ref
  let fresh () = ref ()
  let equal = ( == )
end

(** The [signature] type is used to know how many arguments a PCUIC object
    expects, and what these arguments will become in the ML object. *)

(** We eliminate from terms: 1) types 2) logical parts 3) user-declared implicit
    arguments of a constant of constructor *)

(** Reason why an argument is eliminated during extraction. *)
type kill_reason =
  | Ktype
  | Kprop
  | Kimplicit of GlobRef.t * int  (** n-th arg of a cst or construct *)

(** Whether an argument is kept or eliminated. *)
type sign =
  | Keep
  | Kill of kill_reason

(** Convention: outmost lambda/product gives the head of the list. *)

(** A signature describes which arguments are kept or eliminated. *)
type signature = sign list

(** ML identifiers: regular, dummy, or temporary. *)
type ml_ident =
  | Dummy
  | Id of Id.t
  | Tmp of Id.t

(** {2 ML type expressions} *)

(** Whether a type variable can be instantiated by unification. *)
type tvar_rigidity =
  | Schematic
  | Rigid

(** ML type expressions. *)
type ml_type =
  | Tarr of ml_type * ml_type
  | Tglob of GlobRef.t * ml_type list * ml_ast list
  | Tvar of tvar_rigidity * int
  | Tapp of int * ml_type list
      (** A type variable of arrow kind applied to arguments: the [M A] of
          [mret : forall A, A -> M A], where [M : Type -> Type] is a
          higher-kinded class parameter.  The head is a [Tvar] index.

          Without this node the application collapses to its head and the
          argument types are lost, which is why a higher-kinded carrier used
          to be element-erased. *)
  | Tmeta of ml_meta  (** used during ML type reconstruction *)
  | Thole of int  (** an inference hole of a frozen instantiation *)
  | Tdummy of kill_reason
  | Tunknown
  | Taxiom
  | Tstring

(** Meta-variable for ML type reconstruction. *)
and ml_meta = {
  id : int;
  mutable contents : ml_type option;
}

(** {2 ML inductive types} *)

(** Kind of inductive type. *)
and inductive_kind =
  | Coinductive
  | Standard
  | Record of record_field list
  | TypeClass of record_field list  (** Type class methods *)

(** One field of a record or type class: its projection ([None] when the field
    is anonymous) paired with its ML type.

    The two travel together because extraction selects them together, walking
    the binder names and the constructor's argument types in step and dropping
    the same positions from both.  Splitting them into two lists and zipping
    them back downstream cannot reproduce that: the type list a consumer can
    rebuild from [ip_types] still holds the implicit arguments this selection
    dropped, so the lists have different lengths and the pairing is lost. *)
and record_field = GlobRef.t option * ml_type

(** A [ml_ind_packet] is the miniml counterpart of a [one_inductive_body]. If
    the inductive is logical ([ip_logical = true]), then all other fields are
    unused. Otherwise, [ip_sign] is a signature concerning the arguments of the
    inductive, [ip_vars] contains the names of the type variables surviving in
    ML, [ip_types] contains the ML types of all constructors.

    [ip_consarg_names] stores the binder names for each constructor's arguments,
    extracted from the Rocq kernel ([mind_user_lc]).  Each entry is an array
    indexed by constructor ordinal, containing a list of [Some id] for named
    binders and [None] for anonymous ones.  This enables C++ code generation to
    use meaningful field names (e.g. [d_left], [d_value]) instead of the generic
    positional names [d_a0], [d_a1], etc.

    Example for [Inductive tree := Leaf | Node (left : tree) (v : A) (right : tree)]:
    - [ip_consarg_names.(0) = \[\]]                  (Leaf: no arguments)
    - [ip_consarg_names.(1) = \[Some left; Some v; Some right\]]  (Node) *)
and ml_ind_packet = {
  ip_typename : Id.t;
  ip_consnames : Id.t array;
  ip_logical : bool;
  ip_sign : signature;
  mutable ip_vars : Id.t list;
  ip_types : ml_type list array;
  ip_consarg_names : Id.t option list array;
}

(** Equivalence information for an inductive. *)
and equiv =
  | NoEquiv
  | Equiv of KerName.t
  | RenEquiv of string

(** [ip_nparams] contains the number of parameters. *)
and ml_ind = {
  mutable ind_kind : inductive_kind;
  ind_nparams : int;
  ind_packets : ml_ind_packet array;
  ind_equiv : equiv;
}

(** {2 ML terms} *)
(** We now store some typing information on constructors and cases to avoid
    type-unsafe optimisations. This will be either the type of the applied
    constructor or the type of the head of the match. *)
(** Nota : the constructor [MLtuple] and the extension of [MLcase] to general
    patterns have been proposed by P.N. Tollitte for his Relation Extraction
    plugin. [MLtuple] is currently not used by the main extraction, as well as
    deep patterns. *)

(** A branch in a pattern match. *)
and ml_branch = (ml_ident * ml_type) list * ml_type * ml_pattern * ml_ast

(** ML abstract syntax tree. *)
and ml_ast =
  | MLrel of int
  | MLapp of ml_ast * ml_ast list
  | MLlam of ml_ident * ml_type * ml_ast
  | MLletin of ml_ident * ml_type * ml_ast * ml_ast
  | MLglob of global_use
  | MLcons of ml_type * GlobRef.t * ml_ast list
  | MLtuple of ml_ast list
  | MLcase of ml_type * ml_ast * ml_branch array
  | MLfix of int * (Id.t * ml_type) array * ml_ast array * bool  (** is_cofix *)
  | MLexn of string
  | MLdummy of kill_reason
  | MLaxiom of string
  | MLmagic of ml_magic * ml_ast
  | MLuint of Uint63.t
  | MLfloat of Float64.t
  | MLstring of Pstring.t
  | MLparray of ml_ast array * ml_ast

(** A global at a use.  See miniml.mli. *)
and global_use = {
  callee : GlobRef.t;
  instance : global_instance;
  occurrence : Occurrence.t;
}

and global_instance =
  | Monomorphic
  | Polymorphic of ml_type Scheme.Instantiation.t

(** What an [MLmagic] node is doing.  Extraction inserts these wherever type
    erasure has opened a gap, but not every gap is a coercion, and the two
    kinds must not be confused. *)
and ml_magic =
  | Mcoerce of ml_type * ml_type
    (* [Mcoerce (from, into)]: the term has type [from], the context requires
       [into], and the two do not unify.  This is the representation boundary
       Rocq's [needs_magic] detected, kept with both of its types so the
       backend does not have to rediscover them. *)
  | Mboxed
    (* Not a coercion either: an assertion by the backend that, whatever the
       term's ML type says, its value is physically inside a [std::any] at
       runtime.  Emitted where the C++ calling convention boxes a value behind
       extraction's back (see [crane_erase_fn]'s fallback), so a read of it
       must go through an [any_cast]. *)
  | Mbarrier
    (* Not a coercion: a marker separating two groups of [MLlam] nodes so that
       [collect_lams] stops between them.  Carries no type gap, and nothing
       may be cast on account of it. *)

(** Pattern for pattern matching. *)
and ml_pattern =
  | Pcons of GlobRef.t * ml_pattern list
  | Ptuple of ml_pattern list
  | Prel of int  (** Cf. the idents in the branch. [Prel 1] is the last one. *)
  | Pwild
  | Pusual of GlobRef.t  (** Shortcut for Pcons (r,[Prel n;...;Prel 1]) **)

(** {2 ML declarations} *)

(** One definition of a group of mutually recursive definitions. *)
type ml_fix_def = {fd_ref : GlobRef.t; fd_body : ml_ast; fd_type : ml_type}

(** ML declaration. *)
type ml_decl =
  | Dind of MutInd.t * ml_ind
  | Dtype of GlobRef.t * Id.t list * ml_type
  | Dterm of GlobRef.t * ml_ast * ml_type
  | Dfix of ml_fix_def list

(** ML specification. *)
type ml_spec =
  | Sind of MutInd.t * ml_ind
  | Stype of GlobRef.t * Id.t list * ml_type option
  | Sval of GlobRef.t * ml_ast * ml_type

(** ML signature element. *)
type ml_specif =
  | Spec of ml_spec
  | Smodule of ml_module_type
  | Smodtype of ml_module_type

(** ML module type. *)
and ml_module_type =
  | MTident of ModPath.t
  | MTfunsig of MBId.t * ml_module_type * ml_module_type
  | MTsig of ModPath.t * ml_module_sig
  | MTwith of ml_module_type * ml_with_declaration

(** ML with declaration. *)
and ml_with_declaration =
  | ML_With_type of Id.t list * Id.t list * ml_type
  | ML_With_module of Id.t list * ModPath.t

(** ML module signature. *)
and ml_module_sig = (Label.t * ml_specif) list

(** ML structure element. *)
type ml_structure_elem =
  | SEdecl of ml_decl
  | SEmodule of ml_module
  | SEmodtype of ml_module_type

(** ML module expression. *)
and ml_module_expr =
  | MEident of ModPath.t
  | MEfunctor of MBId.t * ml_module_type * ml_module_expr
  | MEstruct of ModPath.t * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

(** ML module structure. *)
and ml_module_structure = (Label.t * ml_structure_elem) list

(** ML module with expression and type. *)
and ml_module = {
  ml_mod_expr : ml_module_expr;
  ml_mod_type : ml_module_type;
}

(** NB: we do not translate the [mod_equiv] field, since [mod_equiv = mp]
    implies that [mod_expr = MEBident mp]. Same with [msb_equiv]. *)

(** Top-level ML structure. *)
type ml_structure = (ModPath.t * ml_module_structure) list

(** Top-level ML signature. *)
type ml_signature = (ModPath.t * ml_module_sig) list

(** Tracks which unsafe features are needed. *)
type unsafe_needs = {
  mldummy : bool;
  tdummy : bool;
  tunknown : bool;
  magic : bool;
}

(** Language backend descriptor. *)
type language_descr = {
  keywords : Id.Set.t;
  (* names refused only where a declaration reaches global scope *)
  global_scope_keywords : Id.Set.t;
  (* Concerning the source file *)
  file_suffix : string;
  file_naming : ModPath.t -> string;
  (* the second argument is a comment to add to the preamble *)
  preamble : Id.t -> string option -> ModPath.t list -> unsafe_needs -> Pp.t;
  pp_struct : ml_structure -> Pp.t;
  pp_hstruct : ml_structure -> Pp.t;
  (* Concerning a possible interface file *)
  sig_suffix : string option;
  (* the second argument is a comment to add to the preamble *)
  sig_preamble : Id.t -> string option -> ModPath.t list -> unsafe_needs -> Pp.t;
  (* for an isolated declaration print *)
  pp_decl : ml_decl -> Pp.t;
}

module Global_use = struct
  let callee g = g.callee
  let occurrence g = g.occurrence
  let monomorphic callee = {callee; instance = Monomorphic; occurrence = Occurrence.fresh ()}

  let polymorphic callee inst =
    if Scheme.Id.arity (Scheme.Instantiation.scheme inst) = 0 then monomorphic callee
    else {callee; instance = Polymorphic inst; occurrence = Occurrence.fresh ()}

  let with_slots callee scheme slot = polymorphic callee (Scheme.Instantiation.make scheme slot)

  let infer_all callee scheme =
    with_slots callee scheme (fun _ ->
        {Scheme.solution = Scheme.Type (Thole (Scheme.Hole.fresh ())); source = Scheme.Not_written} )

  let identity callee scheme =
    with_slots callee scheme (fun _ -> {Scheme.solution = Scheme.Identity; source = Scheme.Not_written})

  let instantiation g =
    match g.instance with
    | Monomorphic -> None
    | Polymorphic inst -> Some inst

  let fold_slots f g acc =
    match g.instance with
    | Monomorphic -> acc
    | Polymorphic inst -> Scheme.Instantiation.fold f inst acc

  (* What a slot's [Written] evidence stands for in the written list the
     readers were built on: an argument extraction could not read is the
     [Tdummy] it wrote there. *)
  let written_type = function
    | Scheme.Written {observed = Some t; _} -> Some t
    | Scheme.Written {observed = None; _} -> Some (Tdummy Ktype)
    | Scheme.Not_written -> None

  let written_evidence g =
    List.rev
      (fold_slots
         (fun v s acc ->
           match written_type s.Scheme.source with
           | Some t -> (v, t) :: acc
           | None -> acc )
         g [] )

  let map_types f g =
    match g.instance with
    | Monomorphic -> g
    | Polymorphic inst -> {g with instance = Polymorphic (Scheme.Instantiation.map f inst)}

  let slot_types g =
    List.rev
      (fold_slots
         (fun _ {Scheme.solution; source} acc ->
           let acc = match solution with Scheme.Type t -> t :: acc | Scheme.Identity -> acc in
           match source with
           | Scheme.Written {observed = Some t; _} -> t :: acc
           | _ -> acc )
         g [] )

  let iter_types f g = List.iter f (slot_types g)
  let exists_type p g = List.exists p (slot_types g)
end

module Meta = struct
  type late_solution =
    | Fixpoint_codomain
    | Fixpoint_variable
    | Let_lambda_variable
    | Bind_continuation
    | Binder_signature
    | Erased_slot

  let late_solution_name = function
    | Fixpoint_codomain -> "fixpoint codomain"
    | Fixpoint_variable -> "fixpoint variable"
    | Let_lambda_variable -> "let-lambda variable"
    | Bind_continuation -> "bind continuation"
    | Binder_signature -> "binder signature"
    | Erased_slot -> "erased slot"

  let fresh id = {id; contents = None}
  let solved id t = {id; contents = Some t}
  let frozen = ref false
  let counts : (late_solution, int) Hashtbl.t = Hashtbl.create 6

  let solve ?late m t =
    ( match late with
    | Some reason ->
      Hashtbl.replace counts reason (1 + Option.default 0 (Hashtbl.find_opt counts reason))
    | None ->
      if !frozen && Sys.getenv_opt "CRANE_CHECK_IR" <> None then
        CErrors.anomaly
          Pp.(str "Crane: a metavariable of the frozen program was solved for no declared reason.") );
    m.contents <- Some t

  let freeze () =
    frozen := true;
    Hashtbl.reset counts

  let thaw () = frozen := false

  let late_solutions () =
    List.filter_map
      (fun r -> Option.map (fun n -> (r, n)) (Hashtbl.find_opt counts r))
      [Fixpoint_codomain; Fixpoint_variable; Let_lambda_variable; Bind_continuation; Binder_signature; Erased_slot]
end
