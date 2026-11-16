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

(** Core: the language-agnostic functional program extraction produces, and
    the first IR of Crane's pipeline.

    {[ Rocq PCUIC --[extraction.ml]--> Core --[Core passes]--> Core
       --[Translation and the Translation_* modules]--> CppIR
       --[resolution]--> CppAST --[Emit.Print]--> C++ ]}

    Extraction from Rocq's PCUIC first erases everything with no
    computational content -- types, logical ([Prop]) subterms, and
    user-declared implicit arguments -- recording what was removed in a
    {!Core.Signature.t}.  The surviving computation is expressed in these
    families: {!Core.Type} for type expressions, {!Core.Expr} for terms,
    {!Core.Inductive} for inductive declarations, {!Core.Decl} and
    {!Core.Module} for whole definitions and module components.  The Core
    passes ({!Core_passes.Phase}: inlining, dead-code elimination, deduplication,
    specialisation, knot-tying, freezing, normalisation) run over these trees
    before lowering turns them into CppIR.

    The language descends from the intermediate language of Rocq's own
    extraction plugin; Crane extends it (notably
    {!Core.Inductive.Packet}'s constructor argument names, occurrences, and
    use-site instantiations) to carry the extra information the C++ backend
    needs.

    The families are mutually recursive -- a type names a value argument, an
    expression names a type -- so they are defined here together, as
    recursive modules holding (almost) only types; each family's own file
    ([Core.Type], [Core.Expr], ...) re-exports it under its final name, and
    this module itself is not exported from [Core].  Like every module of
    [src/core/], it depends on nothing of the compiler but {!Scheme}. *)

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
        {!Core.Type.Variable}. *)
    type t =
      | Schematic
      | Rigid
  end

  (** An erased type expression, the residue of a PCUIC type after logical
      and type-only content is removed, at the phase ['p] ({!Phase}). *)
  type 'p at =
    | Arrow of {
        parameter : 'p at;
        result : 'p at;
      }  (** a (non-dependent) function arrow *)
    | Global_app of {
        head : GlobRef.t;
        type_arguments : 'p at list;
        index_arguments : 'p Expr.at list;
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
            being reconstructed, made rigid by {!Base.Core_util.rigidify}.

            The two do not unify with each other even at the same index,
            which is the whole point: it is that failure that makes
            {!Base.Core_util.needs_magic} insert a {!Core.Expr.Coerce} where a definition's
            own variable meets a schematic one.  Note that
            {!Base.Core_util.type_subst_list} substitutes both flavours -- rigidity
            constrains unification, not substitution.

            Almost every reader outside {!Base.Core_util} and {!Rocq_to_core.Extraction} ignores
            [rigidity]: the back end does not care which flavour it has. *)
    | Variable_app of {
        head : int;
        arguments : 'p at list;
      }
        (** A type variable of arrow kind applied to arguments: the [M A] of
            [mret : forall A, A -> M A], where [M : Type -> Type] is a
            higher-kinded class parameter.  [head] is a [Variable] index. *)
    | Meta of 'p Meta.t
        (** a unification variable of type reconstruction; only an
            [extracted] type can hold one, since only an [extracted] cell can
            be made *)
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
            solved, as {!Core_passes.Phase.freeze} hands it on.  Immutable, and read
            as erased.  The annotations that shared the metavariable share the
            [Open.t], so a reader that fills it from other evidence fills it
            wherever it is written ({!Base.Type_util.fill_holes}).  Unlike a
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
      made and solved only through {!Core.Extracted.Meta}. *)
  type 'p t = private {
    id : int;
    mutable contents : 'p Type.at option;
    phase : 'p Phase.is_extracted;  (** what makes a frozen cell impossible *)
  }

  (** [make id contents] is the cell [id] holding [contents]: only an
      extracted one, so that a frozen type holds none. *)
  val make : int -> Phase.extracted Type.at option -> Phase.extracted t

  (** [set m t] solves [m] to [t]. *)
  val set : 'p t -> 'p Type.at -> unit
end = struct
  type 'p t = {
    id : int;
    mutable contents : 'p Type.at option;
    phase : 'p Phase.is_extracted;
  }

  let make id contents = {id; contents; phase = Phase.Extracted}
  let set m t = m.contents <- Some t
end

and Record : sig
  module Field : sig
    (** One field of a record or type class: its [projection] ([None] when
        the field is anonymous) and its type.  Extraction selects the two
        together -- walking binder names and constructor argument types in
        step, dropping the same positions from both -- so they are stored
        together; a consumer that zips a name list against a type list
        rebuilt from {!Core.Inductive.Packet.constructor_argument_types} gets a
        length mismatch, because that list still holds the implicit
        arguments the selection dropped. *)
    type t = {
      projection : GlobRef.t option;
      type_ : Phase.frozen Type.at;
    }
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
        names, [signature] the {!Core.Signature.t} of the inductive's own
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
      constructor_argument_types : Phase.frozen Type.at list array;
      constructor_argument_names : Id.t option list array;
    }
  end

  (** A whole (possibly mutual) inductive definition: [kind] its
      classification, [parameter_count] the number of uniform parameters,
      [packets] one {!Core.Inductive.Packet.t} per mutually-defined body, and [equivalence]
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

      [Construct] and [Match] deliberately carry a {!Core.Type.t} -- the type of
      the applied constructor, or of the matched head -- so that later
      optimisations remain type-safe.  [Tuple] and the extension of [Match]
      to general patterns come from P.N. Tollitte's Relation Extraction
      plugin; [Tuple] and deep patterns are unused by the main extraction. *)
  type 'p at =
    | Bound_variable of {
        index : int;
        occurrence : Occurrence.t;
      }
        (** The de Bruijn index of the binder read, and the occurrence
            telling this read apart from every other one: a pass moving a
            read under other binders keeps it, so what is decided of a read in
            Core is found again where the read is generated. *)
    | Apply of {
        callee : 'p at;
        arguments : 'p at list;
      }
    | Lambda of {
        parameter : Binder_name.t;
        parameter_type : 'p Type.at;
        body : 'p at;
      }
    | Let of {
        binder : Binder_name.t;
        binder_type : 'p Type.at;
        value : 'p at;
        body : 'p at;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this let apart from every other one in the
            program, kept by a pass rebuilding it as a fixpoint's is: two lets
            bound to one name in one definition are still two. *)
    | Global of 'p Global_use.at
        (** a use of a global, with what the use instantiates the global's
            type scheme at *)
    | Construct of {
        result_type : 'p Type.at;
        constructor : GlobRef.t;
        arguments : 'p at list;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this construction apart from every other one
            in the program, kept by a pass rebuilding it as a match's is: two
            constructions of one value in one definition are still two. *)
    | Tuple of 'p at list
    | Match of {
        scrutinee_type : 'p Type.at;
        scrutinee : 'p at;
        branches : 'p Match.Branch.at array;
        occurrence : Occurrence.t;
      }
        (** [occurrence] tells this match apart from every other one in the
            program, kept by a pass rebuilding it as a let's is: the binders
            of one branch at one level in two matches are still two. *)
    | Fixpoint of 'p Recursion.Group.at  (** a block of mutually recursive functions *)
    | Cofixpoint of 'p Recursion.Group.at
        (** a block of mutually corecursive functions *)
    | Runtime_error of string  (** raised for an unrealisable term *)
    | Erased_value of Erasure_reason.t  (** the value of an erased slot *)
    | Axiom_value of string  (** a value left abstract by an axiom *)
    | Coerce of {
        source_type : 'p Type.at;
        target_type : 'p Type.at;
        value : 'p at;
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
        value : 'p at;
        occurrence : Occurrence.t;
      }
        (** Not a coercion: an assertion by the backend that, whatever
            [value]'s type says, it is physically inside a [std::any] at
            runtime.  Emitted where the C++ calling convention boxes a value
            behind extraction's back (see [crane_erase_fn]'s fallback), so a
            read of it must go through an [any_cast]. *)
    | Lambda_group_barrier of {
        value : 'p at;
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
        elements : 'p at array;
        default : 'p at;
      }
    | Numeral of {
        inductive : GlobRef.t;
        value : Z.t;
      }
        (** A value of a numeral inductive -- one [Crane Extract Numeral]
            registers: what a numeral converter applied to a digit chain
            computes ({!Core_passes.Numeral_literal}). *)
end =
  Expr

and Global_use : sig
  (** A use of a declaration with no scheme variable is [Core.Global_use.Monomorphic].  Any
      other is [Core.Global_use.Polymorphic], with an instantiation at the callee's scheme:
      one slot per variable, indexed by {!Scheme.Var.t}, each holding what
      the use solved the variable to -- a type that may contain
      {!Core.Type.Hole}s but no [Core.Type.Meta], or [Identity] for a rigid self-call
      -- and the argument the source wrote at the variable's binder, if it
      reached it.  There is no list of type arguments: which of them C++
      writes, and where, is a question about the callee's declaration, not
      about this use. *)
  type 'p instance =
    | Monomorphic
    | Polymorphic of 'p Type.at Scheme.Instantiation.t

  (** A global named at a use: the callee, and what the use means for the
      callee's type scheme.  Built only through {!Core.Global_use}; a reader
      that needs only the callee matches [Global {callee; _}] and never sees
      the rest. *)
  type 'p at = private {
    callee : GlobRef.t;
    instance : 'p instance;
    occurrence : Occurrence.t;
  }

  val make : GlobRef.t -> 'p instance -> Occurrence.t -> 'p at
end = struct
  type 'p instance =
    | Monomorphic
    | Polymorphic of 'p Type.at Scheme.Instantiation.t

  type 'p at = {
    callee : GlobRef.t;
    instance : 'p instance;
    occurrence : Occurrence.t;
  }

  let make callee instance occurrence = {callee; instance; occurrence}
end

and Match : sig
  module Branch : sig
    (** A single {!Core.Expr.Match} branch.  [binders] are the variables bound by
        [pattern] paired with their types, [result_type] is the branch's
        result type, and [body] the term run when [pattern] matches. *)
    type 'p at = {
      binders : (Binder_name.t * 'p Type.at) list;
      result_type : 'p Type.at;
      pattern : Pattern.t;
      body : 'p Expr.at;
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
            last of {!Core.Match.Branch.binders} *)
    | Wildcard
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

  (** Per-argument decisions for a PCUIC object, one {!Core.Signature.Argument.t} per
      argument, outermost first: it tells how many arguments the object
      expects and what each becomes. *)
  type t = Argument.t list

  module Declaration : sig
    (** The interface view of a Core entity, used when emitting signatures.
        [Inductive] specifies an inductive; [Type] a type name (with an
        optional definition, [None] when abstract); [Value] a value with its
        body and type. *)
    type 'p at =
      | Inductive of {
          entity : MutInd.t;
          definition : Inductive.t;
        }
      | Type of {
          entity : GlobRef.t;
          parameters : Id.t list;
          body : 'p Type.at option;
        }
      | Value of {
          entity : GlobRef.t;
          body : 'p Expr.at;
          type_ : 'p Type.at;
        }
  end
end =
  Signature

and Recursion : sig
  module Definition : sig
    (** One definition of a group of mutually recursive definitions. *)
    type 'p at = {
      entity : GlobRef.t;
      body : 'p Expr.at;
      type_ : 'p Type.at;
    }
  end

  module Member : sig
    (** One function of a local recursive group: the name it is bound to,
        its type and its body. *)
    type 'p at = {
      name : Id.t;
      type_ : 'p Type.at;
      body : 'p Expr.at;
    }
  end

  module Group : sig
    (** A block of local mutually (co)recursive functions, the value of an
        {!Core.Expr.Fixpoint} or {!Core.Expr.Cofixpoint}: its [members], in binding
        order -- the last is the innermost binder, so in every body the
        member [i] of [n] is read as [Bound_variable (n - i)] -- the member
        [selected] the block evaluates to, by its position, and the
        occurrence telling this block apart from every other one in the
        program: a pass rebuilding it keeps it, so the plan made of the
        block and the code made of it name one block.  Built only through
        {!make}, so a group has a member and selects one it has. *)
    type 'p at = private {
      selected : int;
      members : 'p Member.at array;
      occurrence : Occurrence.t;
    }

    (** [make ~selected members occurrence]; raises [Invalid_argument] when
        [members] is empty or has no member [selected]. *)
    val make : selected:int -> 'p Member.at array -> Occurrence.t -> 'p at
  end
end = struct
  module Definition = struct
    type 'p at = {
      entity : GlobRef.t;
      body : 'p Expr.at;
      type_ : 'p Type.at;
    }
  end

  module Member = struct
    type 'p at = {
      name : Id.t;
      type_ : 'p Type.at;
      body : 'p Expr.at;
    }
  end

  module Group = struct
    type 'p at = {
      selected : int;
      members : 'p Member.at array;
      occurrence : Occurrence.t;
    }

    let make ~selected members occurrence =
      if selected < 0 || selected >= Array.length members then
        invalid_arg "Core.Recursion.Group.make: no such member";
      {selected; members; occurrence}
  end
end

and Decl : sig
  (** A concrete, defined top-level entity. *)
  type 'p at =
    | Inductive of {
        entity : MutInd.t;
        definition : Inductive.t;
      }
    | Type_alias of {
        entity : GlobRef.t;
        parameters : Id.t list;
        body : 'p Type.at;
      }  (** a type abbreviation: its type-variable names and body *)
    | Value of {
        entity : GlobRef.t;
        body : 'p Expr.at;
        type_ : 'p Type.at;
      }  (** a single term definition *)
    | Recursive_group of 'p Recursion.Definition.at Nonempty.t
        (** mutually recursive definitions, in definition order *)
end =
  Decl

and Module_type : sig
  (** A module type. *)
  type 'p at =
    | Path of ModPath.t
    | Functor of {
        parameter : MBId.t;
        parameter_type : 'p at;
        result : 'p at;
      }  (** a functor signature *)
    | Signature of {
        path : ModPath.t;
        items : 'p Module_signature.at;
      }  (** an explicit signature *)
    | Refined of {
        base : 'p at;
        refinement : 'p Refinement.at;
      }  (** a module type refined by a [with] constraint *)
end =
  Module_type

and Refinement : sig
  (** A [with] refinement on a module type, fixing a type component or a
      sub-module component, by path. *)
  type 'p at =
    | Type_equation of {
        path : Id.t list;
        parameters : Id.t list;
        definition : 'p Type.at;
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
  type 'p at =
    | Declaration of 'p Signature.Declaration.at
    | Module of 'p Module_type.at
    | Module_type of 'p Module_type.at
end =
  Signature_item

and Module_signature : sig
  (** The body of a module signature: its components paired with their
      labels. *)
  type 'p at = (Label.t * 'p Signature_item.at) list
end =
  Module_signature

and Structure_item : sig
  (** A single component of a module implementation: a definition, a nested
      module, or a nested module-type binding. *)
  type 'p at =
    | Declaration of 'p Decl.at
    | Module of 'p Module_binding.at
    | Module_type of 'p Module_type.at
end =
  Structure_item

and Module_expr : sig
  (** A module expression (implementation). *)
  type 'p at =
    | Path of ModPath.t
    | Functor of {
        parameter : MBId.t;
        parameter_type : 'p Module_type.at;
        body : 'p at;
      }
    | Structure of {
        path : ModPath.t;
        items : 'p Module_structure.at;
      }
    | Apply of {
        functor_ : 'p at;
        argument : 'p at;
      }
end =
  Module_expr

and Module_structure : sig
  (** The body of a module structure: its elements paired with their
      labels. *)
  type 'p at = (Label.t * 'p Structure_item.at) list
end =
  Module_structure

and Module_binding : sig
  (** A module binding: its implementation and its type.  The kernel's
      [mod_equiv] field is not translated, since [mod_equiv = mp] would imply
      [mod_expr = MEBident mp] (likewise [msb_equiv]). *)
  type 'p at = {
    expr : 'p Module_expr.at;
    type_ : 'p Module_type.at;
  }
end =
  Module_binding
