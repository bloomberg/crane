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

(** Core: the language-agnostic functional program extraction produces.

    The pipeline is

    {[ Rocq PCUIC --[extraction.ml]--> Core --[translation.ml]--> CppIR
       --[cpp.ml]--> C++ ]}

    Extraction from Rocq's PCUIC first erases everything with no
    computational content -- types, logical ([Prop]) subterms, and
    user-declared implicit arguments -- recording what was removed in a
    {!Signature.t}.  The surviving computation is expressed in these
    families: {!Type} for type expressions, {!Expr} for terms, {!Inductive}
    for inductive declarations, {!Decl} and {!Module} for whole definitions
    and module components.  Core-level optimisations (inlining, dead-code
    elimination, currying fixes) run over these trees before {!Translation}
    lowers them to {!Cpp_ir}.

    The language descends from Rocq's own extraction plugin's Core; Crane
    extends it (notably {!Inductive.Packet}'s constructor argument names) to
    carry the extra information the C++ backend needs.

    The families are mutually recursive -- a type names a value argument, an
    expression names a type -- so they are defined here together, as
    recursive modules holding only types; each family's own file
    ([Core.Type], [Core.Expr], ...) re-exports it under its final name. *)

open Names

module rec Erasure_reason : sig
  (** Why a PCUIC argument or subterm carries no computational content and
      is therefore erased during extraction. *)
  type t =
    | Type_argument  (** a type argument *)
    | Proof  (** a logical ([Prop]) part *)
    | Configured_implicit of {
        entity : GlobRef.t;
        position : int;
      }
        (** the [position]-th argument of the constant or constructor
            [entity], which the user declared implicit *)
end =
  Erasure_reason

and Binder_name : sig
  (** A Core binder name. *)
  type t =
    | Anonymous  (** an erased or unused argument: no meaningful name survived *)
    | Source of Id.t  (** a Rocq identifier *)
    | Generated of Id.t  (** a temporary introduced by a Core transformation *)
end =
  Binder_name

and Type : sig
  module Rigidity : sig
    (** Whether a type variable can be instantiated by unification.  See
        {!Type.Variable}. *)
    type t =
      | Schematic
      | Rigid
  end

  (** An erased type expression, the residue of a PCUIC type after logical
      and type-only content is removed. *)
  type t =
    | Arrow of {
        parameter : t;
        result : t;
      }  (** a (non-dependent) function arrow *)
    | Global_app of {
        head : GlobRef.t;
        type_arguments : t list;
        index_arguments : Expr.t list;
      }
        (** the named inductive or type constant [head] applied to type
            arguments, with the value arguments of its indexed or dependent
            positions *)
    | Variable of {
        rigidity : Rigidity.t;
        variable : int;
      }
        (** A De Bruijn type variable.  [Core.Type.Rigidity.Schematic] is a variable of some
            other constant's type scheme, standing to be instantiated when that
            scheme is instantiated; [Core.Type.Rigidity.Rigid] is one of the definition currently
            being reconstructed, made rigid by {!Mlutil.rigidify}.

            The two do not unify with each other even at the same index,
            which is the whole point: it is that failure that makes
            {!Mlutil.needs_magic} insert a {!Expr.Coerce} where a definition's
            own variable meets a schematic one.  Note that
            {!Mlutil.type_subst_list} substitutes both flavours -- rigidity
            constrains unification, not substitution.

            Almost every reader outside {!Mlutil} and {!Extraction} ignores
            [rigidity]: the back end does not care which flavour it has. *)
    | Variable_app of {
        head : int;
        arguments : t list;
      }
        (** A type variable of arrow kind applied to arguments: the [M A] of
            [mret : forall A, A -> M A], where [M : Type -> Type] is a
            higher-kinded class parameter.  [head] is a [Variable] index. *)
    | Meta of Meta.t  (** a unification variable of type reconstruction *)
    | Hole of int
        (** An inference hole: a scheme variable a use's local unification
            left unsolved, frozen into the use's instantiation in place of the
            metavariable.  Unlike a [Meta] it is immutable and shared with no
            other term; unlike a [Variable] it names no variable of any
            scheme; and it is not [Unknown], [Erased] or [Axiom], each of which
            says something a hole does not.  Only an instantiation and the
            types a reader computes from one may hold it; a consumer resolves
            it from other evidence, leaves the parameter to deduction, or
            reports it. *)
    | Open of Open.t
        (** An annotation reconstruction left open: a metavariable nothing
            solved, as {!Core_phase.freeze} hands it on.  Immutable, and read
            as erased.  The annotations that shared the metavariable share the
            [Open.t], so a reader that fills it from other evidence fills it
            wherever it is written ({!Ml_type_util.fill_holes}).  Unlike a
            [Hole] nothing is owed to it: no instantiation slot stands behind
            it, and a consumer with nothing to fill it from spells it erased.
            No [Meta] survives freezing; this is what becomes of the open
            ones. *)
    | Erased of Erasure_reason.t  (** a type slot that was erased, and why *)
    | Unknown  (** a type inference gave up on *)
    | Axiom  (** a type left abstract by an axiom *)
    | String  (** the primitive string type *)
end =
  Type

and Meta : sig
  (** A mutable type metavariable used while reconstructing types: [id]
      identifies it and [contents] is filled in with the resolved type once
      unification succeeds (staying [None] until then).  Read anywhere, but
      made and solved only through {!Core.Meta}. *)
  type t = {
    id : int;
    mutable contents : Type.t option;
  }
end =
  Meta

and Record : sig
  module Field : sig
    (** One field of a record or type class: its projection ([None] when
        the field is anonymous) paired with its type.  Extraction selects the
        two together -- walking binder names and constructor argument types
        in step, dropping the same positions from both -- so they are stored
        together; a consumer that zips a name list against a type list
        rebuilt from {!Inductive.Packet.constructor_argument_types} gets a
        length mismatch, because that list still holds the implicit
        arguments the selection dropped. *)
    type t = GlobRef.t option * Type.t
  end
end =
  Record

and Inductive : sig
  module Kind : sig
    (** How an inductive type should be treated by the backend. [Inductive]
        is an ordinary (finite) inductive; [Coinductive] a lazily-unfolded
        one; [Record] a single-constructor inductive presented with named
        projections (the list gives its fields); and [Type_class] a record
        standing for a Rocq type class, whose fields are its methods. *)
    type t =
      | Coinductive
      | Inductive
      | Record of Record.Field.t list
      | Type_class of Record.Field.t list
  end

  module Equivalence : sig
    (** How an inductive relates to another already-extracted one, used to
        share definitions. [Distinct] means it is emitted on its own;
        [Equivalent_to kn] redirects it to the kernel name [kn] of an
        equivalent inductive; [Equivalent_in_renamed_module s] redirects to
        an inductive living in the module renamed [s]. *)
    type t =
      | Distinct
      | Equivalent_to of KerName.t
      | Equivalent_in_renamed_module of string
  end

  module Packet : sig
    (** One of the (mutually) defined inductive types, the counterpart of a
        kernel [one_inductive_body].  When [logical] holds the type has no
        computational content and the other fields are unused; otherwise
        [name] is the type's name, [constructor_names] the constructor
        names, [Core.Signature.t] the {!Signature.t} of the inductive's own
        arguments, [type_variables] the names of the type variables
        surviving extraction, and [constructor_argument_types] the argument
        types of each constructor (indexed by constructor ordinal).

        [constructor_argument_names]: for each constructor (indexed the same
        way), its argument binder names as the kernel has them
        ([mind_user_lc]), [Some id] for a named binder and [None] for an
        anonymous one.  This lets C++ generation emit meaningful field names
        (e.g. [d_left], [d_value]) instead of positional [d_a0], [d_a1].  For
        [Inductive tree := Leaf | Node (left : tree) (v : A) (right : tree)]
        it is [[| []; [Some left; Some v; Some right] |]]. *)
    type t = {
      name : Id.t;
      constructor_names : Id.t array;
      logical : bool;
      signature : Signature.t;
      mutable type_variables : Id.t list;
      constructor_argument_types : Type.t list array;
      constructor_argument_names : Id.t option list array;
    }
  end

  (** A whole (possibly mutual) inductive definition: [kind] its
      classification, [parameter_count] the number of uniform parameters,
      [packets] one {!Packet.t} per mutually-defined body, and [equivalence]
      any sharing or redirection information. *)
  type t = {
    mutable kind : Kind.t;
    parameter_count : int;
    packets : Packet.t array;
    equivalence : Equivalence.t;
  }
end =
  Inductive

and Expr : sig
  (** An erased term -- the computational residue of a PCUIC term.

      [Construct] and [Match] deliberately carry a {!Type.t} -- the type of
      the applied constructor, or of the matched head -- so that later
      optimisations remain type-safe.  [Tuple] and the extension of [Match]
      to general patterns come from P.N. Tollitte's Relation Extraction
      plugin; [Tuple] and deep patterns are unused by the main extraction. *)
  type t =
    | Bound_variable of {
        index : int;
        occurrence : Occurrence.t;
      }
        (** The de Bruijn index of the binder read, and the occurrence
            telling this read apart from every other one: a pass moving a
            read under other binders keeps it, so what is decided of a read in
            Core is found again where the read is generated. *)
    | Apply of {
        callee : t;
        arguments : t list;
      }
    | Lambda of {
        parameter : Binder_name.t;
        parameter_type : Type.t;
        body : t;
      }
    | Let of {
        binder : Binder_name.t;
        binder_type : Type.t;
        value : t;
        body : t;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this let apart from every other one in the
            program, kept by a pass rebuilding it as a fixpoint's is: two lets
            bound to one name in one definition are still two. *)
    | Global of Global_use.t
        (** a use of a global, with what the use instantiates the global's
            type scheme at *)
    | Construct of {
        result_type : Type.t;
        constructor : GlobRef.t;
        arguments : t list;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this construction apart from every other one
            in the program, kept by a pass rebuilding it as a match's is: two
            constructions of one value in one definition are still two. *)
    | Tuple of t list
    | Match of {
        scrutinee_type : Type.t;
        scrutinee : t;
        branches : Match.Branch.t array;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this match apart from every other one in the
            program, kept by a pass rebuilding it as a let's is: the binders
            of one branch at one level in two matches are still two. *)
    | Fixpoint of {
        selected : int;
        functions : (Id.t * Type.t) array;
        bodies : t array;
        occurrence : Occurrence.t;
      }
        (** A block of mutually recursive functions: the function selected,
            the group's binders and bodies, and the occurrence telling this
            fixpoint apart from every other one in the program: a pass
            rebuilding it keeps it, so the plan made of the fixpoint and the
            code made of it name one fixpoint. *)
    | Cofixpoint of {
        selected : int;
        functions : (Id.t * Type.t) array;
        bodies : t array;
        occurrence : Occurrence.t;
      }  (** A block of mutually corecursive functions, as [Fixpoint]. *)
    | Runtime_error of string  (** raised for an unrealisable term *)
    | Erased_value of Erasure_reason.t  (** the value of an erased slot *)
    | Axiom_value of string  (** a value left abstract by an axiom *)
    | Coerce of {
        source_type : Type.t;
        target_type : Type.t;
        value : t;
        occurrence : Occurrence.t;
      }
        (** An unsafe coercion at a type gap opened by erasure: [value] has
            type [source_type], the context requires [target_type], and the
            two do not unify.  Both types are kept so that a backend can see
            exactly which representation boundary is being crossed instead of
            rediscovering it.  [occurrence] tells this crossing apart from
            every other one, so that what is planned of the position it fills
            is found again where it is lowered. *)
    | Boxed_value of {
        value : t;
        occurrence : Occurrence.t;
      }
        (** Not a coercion: an assertion by the backend that, whatever
            [value]'s type says, it is physically inside a [std::any] at
            runtime.  Emitted where the C++ calling convention boxes a value
            behind extraction's back (see [crane_erase_fn]'s fallback), so a
            read of it must go through an [any_cast]. *)
    | Lambda_group_barrier of {
        value : t;
        occurrence : Occurrence.t;
      }
        (** Not a coercion but a separator, placed between two groups of
            [Lambda] nodes so that a backend collecting consecutive lambdas
            stops between them.  There is no type gap here and nothing may be
            cast on account of it. *)
    | UInt63 of Uint63.t
    | Float64 of Float64.t
    | String of Pstring.t
    | Persistent_array of {
        elements : t array;
        default : t;
      }
    | Numeral of {
        inductive : GlobRef.t;
        value : Z.t;
      }
        (** A value of a numeral inductive -- one [Crane Extract Numeral]
            registers: what a numeral converter applied to a digit chain
            computes ({!Numeral_literal}). *)
end =
  Expr

and Global_use : sig
  (** A use of a declaration with no scheme variable is [Core.Global_use.Monomorphic].  Any
      other is [Core.Global_use.Polymorphic], with an instantiation at the callee's scheme:
      one slot per variable, indexed by {!Scheme.Var.t}, each holding what
      the use solved the variable to -- a type that may contain
      {!Type.Hole}s but no [Type.Meta], or [Identity] for a rigid self-call
      -- and the argument the source wrote at the variable's binder, if it
      reached it.  There is no list of type arguments: which of them C++
      writes, and where, is a question about the callee's declaration, not
      about this use. *)
  type instance =
    | Monomorphic
    | Polymorphic of Type.t Scheme.Instantiation.t

  (** A global named at a use: the callee, and what the use means for the
      callee's type scheme.  Built only through {!Core.Global_use}; a reader
      that needs only the callee matches [Global {callee; _}] and never sees
      the rest. *)
  type t = {
    callee : GlobRef.t;
    instance : instance;
    occurrence : Occurrence.t;
  }
end =
  Global_use

and Match : sig
  module Branch : sig
    (** A single {!Expr.Match} branch.  [binders] are the variables bound by
        [pattern] paired with their types, [result_type] is the branch's
        result type, and [body] the term run when [pattern] matches. *)
    type t = {
      binders : (Binder_name.t * Type.t) list;
      result_type : Type.t;
      pattern : Pattern.t;
      body : Expr.t;
    }
  end
end =
  Match

and Pattern : sig
  (** A match pattern. *)
  type t =
    | Constructor of {
        constructor : GlobRef.t;
        fields : t list;
      }
    | Tuple of t list
    | Bound_variable of int
        (** a branch binder by De Bruijn index: [Bound_variable 1] is the
            last of {!Match.Branch.binders} *)
    | Wildcard
    | Shallow_constructor of GlobRef.t
        (** shorthand for [Constructor] binding every argument in order:
            [Constructor {constructor; fields = [Bound_variable n; ...;
            Bound_variable 1]}] *)
end =
  Pattern

and Signature : sig
  module Argument : sig
    (** Fate of a single PCUIC argument once extraction has run: kept as a
        [Runtime] argument, or [Erased] with the recorded reason. *)
    type t =
      | Runtime
      | Erased of Erasure_reason.t
  end

  (** Per-argument decisions for a PCUIC object, one {!Argument.t} per
      argument, outermost first: it tells how many arguments the object
      expects and what each becomes. *)
  type t = Argument.t list

  module Declaration : sig
    (** The interface view of a Core entity, used when emitting signatures.
        [Inductive] specifies an inductive; [Type] a type name (with an
        optional definition, [None] when abstract); [Value] a value with its
        body and type. *)
    type t =
      | Inductive of {
          entity : MutInd.t;
          definition : Inductive.t;
        }
      | Type of {
          entity : GlobRef.t;
          parameters : Id.t list;
          body : Type.t option;
        }
      | Value of {
          entity : GlobRef.t;
          body : Expr.t;
          type_ : Type.t;
        }
  end
end =
  Signature

and Recursion : sig
  module Definition : sig
    (** One definition of a group of mutually recursive definitions. *)
    type t = {
      entity : GlobRef.t;
      body : Expr.t;
      type_ : Type.t;
    }
  end
end =
  Recursion

and Decl : sig
  (** A concrete, defined top-level entity. *)
  type t =
    | Inductive of {
        entity : MutInd.t;
        definition : Inductive.t;
      }
    | Type_alias of {
        entity : GlobRef.t;
        parameters : Id.t list;
        body : Type.t;
      }  (** a type abbreviation: its type-variable names and body *)
    | Value of {
        entity : GlobRef.t;
        body : Expr.t;
        type_ : Type.t;
      }  (** a single term definition *)
    | Recursive_group of Recursion.Definition.t Nonempty.t
        (** mutually recursive definitions, in definition order *)
end =
  Decl

and Module_type : sig
  (** A module type. *)
  type t =
    | Path of ModPath.t
    | Functor of {
        parameter : MBId.t;
        parameter_type : t;
        result : t;
      }  (** a functor signature *)
    | Signature of {
        path : ModPath.t;
        items : Module_signature.t;
      }  (** an explicit signature *)
    | Refined of {
        base : t;
        refinement : Refinement.t;
      }  (** a module type refined by a [with] constraint *)
end =
  Module_type

and Refinement : sig
  (** A [with] refinement on a module type, fixing a type component or a
      sub-module component, by path. *)
  type t =
    | Type_equation of {
        path : Id.t list;
        parameters : Id.t list;
        definition : Type.t;
      }
    | Module_equation of {
        path : Id.t list;
        definition : ModPath.t;
      }
end =
  Refinement

and Signature_item : sig
  (** A single component of a module signature: a declaration, a nested
      module, or a nested module type. *)
  type t =
    | Declaration of Signature.Declaration.t
    | Module of Module_type.t
    | Module_type of Module_type.t
end =
  Signature_item

and Module_signature : sig
  (** The body of a module signature: its components paired with their
      labels. *)
  type t = (Label.t * Signature_item.t) list
end =
  Module_signature

and Structure_item : sig
  (** A single component of a module implementation: a definition, a nested
      module, or a nested module-type binding. *)
  type t =
    | Declaration of Decl.t
    | Module of Module_binding.t
    | Module_type of Module_type.t
end =
  Structure_item

and Module_expr : sig
  (** A module expression (implementation). *)
  type t =
    | Path of ModPath.t
    | Functor of {
        parameter : MBId.t;
        parameter_type : Module_type.t;
        body : t;
      }
    | Structure of {
        path : ModPath.t;
        items : Module_structure.t;
      }
    | Apply of {
        functor_ : t;
        argument : t;
      }
end =
  Module_expr

and Module_structure : sig
  (** The body of a module structure: its elements paired with their
      labels. *)
  type t = (Label.t * Structure_item.t) list
end =
  Module_structure

and Module_binding : sig
  (** A module binding: its implementation and its type.  The kernel's
      [mod_equiv] field is not translated, since [mod_equiv = mp] would imply
      [mod_expr = MEBident mp] (likewise [msb_equiv]). *)
  type t = {
    expr : Module_expr.t;
    type_ : Module_type.t;
  }
end =
  Module_binding
