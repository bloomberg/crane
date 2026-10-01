(* A type-level [Definition] under a [Context] mentions an inductive from the
   same Section, and is emitted as a file-scope alias at the erased names:

     using Dbox = std::pair<Dval<ptr>, Nat>;   // ptr == std::any

   [dval] itself is parameterised correctly, so a value built at the resolved
   instantiation is well-formed and the alias it has to meet is not: the
   diagnostic is a conversion from [Dval<typename PointerV<natIPtr>::ptr>] to
   [Dval<std::any>].

   Distinct from inductive_payload_from_same_section, which is the same
   dependence one category over: that closure runs over the constructor
   payloads of inductives, and an alias has no constructors, so it is outside
   the quantifier however far the closure reaches.  A fix quantified over one
   syntactic category cannot reach a defect in another.

   The import list is not harness configuration -- it selects the emission
   path.

   Fixed: the closure was generalised from an inductive's constructor payloads
   to any type global's definition -- [Table.promoted_type_params] and
   [Table.get_type_class_args] are now keyed by globref and reach a type-level
   [Definition] through its right-hand side, recorded at extraction by
   [Table.add_type_alias_body].  [Gen_decls.gen_type_alias] gives the alias the
   promoted variables as trailing template parameters, which is where
   [Translation.ind_promoted_type_args] passes them, and [record_class_shape]
   accepts a [Const] conclusion head so [packed : @dbox natIPtr] says which
   instance the [ptr] inside belongs to. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ExtLib Require Import Structures.Monad.

Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type := | Ok : A -> EOU A | Err : nat -> EOU A.
Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret  := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end |}.

Class IPtr :=
  { iptr : Type ; zero_iptr : iptr ; from_Z : nat -> EOU iptr
  ; to_Z : iptr -> nat }.

(* [nil_prov] and [null] are not decoration: without a second field an
   instance of a one-Type-field class generates no struct at all, and the
   defect needs the target to exist and be right. *)
Class Provenance := { prov : Type ; nil_prov : prov }.

Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.

Class PI (P : Provenance) (PT : Pointer P) :=
  { ptr_to_int : @ptr P PT -> nat
  ; int_to_ptr : nat -> @prov P -> EOU (@ptr P PT) }.

Section withIPtr.
  Context {IP : IPtr}.

  #[global] Instance ProvenanceV : Provenance :=
    {| prov := bool ; nil_prov := false |}.

  #[global] Instance PointerV : @Pointer ProvenanceV :=
    {| ptr := (iptr * prov)%type ; null := (zero_iptr, nil_prov) |}.

  #[global] Instance PIV : @PI ProvenanceV PointerV :=
    {| ptr_to_int := fun p => to_Z (fst p)
     ; int_to_ptr := fun i pr => bind (from_Z i) (fun a => ret (a, pr)) |}.

  (* The inductive is declared under the section's [Context], and one of its
     constructors carries a field of that context variable's class. *)
  Variant dval : Type :=
    | DPtr (p : @ptr ProvenanceV PointerV)
    | DNat (n : nat).

  (* A type-level [Definition] in the same Section.  It is not an inductive:
     it has no constructor payloads for a closure over them to run over. *)
  Definition dbox : Type := (dval * nat)%type.
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module TypeAliasOfSectionInductive.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition packed : @dbox natIPtr := (@DPtr natIPtr the_null, 7).

  Definition run : nat :=
    match fst packed with
    | DPtr p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
    | DNat n => n
    end.
End TypeAliasOfSectionInductive.

Set Crane Format Style "None".
Crane Extraction "type_alias_of_section_inductive" TypeAliasOfSectionInductive.
