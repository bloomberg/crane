(* A parameterised type-level [Definition] under a [Context], one of whose
   parameters is phantom -- the rendered right-hand side never spells the
   event family [E], so it is declared [typename E = void].  The promoted
   variables the body depends on are appended after it:

     template <typename E = void, typename ptr>
     using dfun = std::function<Nat(Dval<ptr>)>;

   which is ill-formed: a defaulted template parameter may not be followed by
   a non-defaulted one.  The alias then does not exist and every use of it is
   a second error.

   A use omits a phantom argument entirely (see [Ml_type_util.written_type_args]),
   so the default is load-bearing and the phantom parameter has to stay last.
   The promoted parameters go before it, not after -- appending is right at
   the call sites, where the phantom position is not written either, and wrong
   at the declaration.

   The import list is not harness configuration -- it selects the emission
   path. *)

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

  (* A parameterised alias whose parameter the right-hand side never spells:
     [E] is phantom, so it is emitted with a default. *)
  Definition dfun (E : Type -> Type) : Type := dval -> nat.
End withIPtr.

#[global] Instance natIPtr : IPtr :=
  {| iptr := nat ; zero_iptr := 0 ; from_Z := fun n => ret n
   ; to_Z := fun n => n |}.

Module AliasPhantomParamBeforePromoted.
  Definition the_null : @ptr ProvenanceV (@PointerV natIPtr) :=
    @null ProvenanceV (@PointerV natIPtr).

  Definition handler : @dfun natIPtr (fun A => A) :=
    fun d =>
      match d with
      | DPtr p => @ptr_to_int ProvenanceV (@PointerV natIPtr) (@PIV natIPtr) p
      | DNat n => n
      end.

  (* Bound rather than written inline: a constructor call inside [run] would
     have no resolution for [ptr], which is a different defect. *)
  Definition arg : @dval natIPtr := @DPtr natIPtr the_null.

  Definition run : nat := handler arg.
End AliasPhantomParamBeforePromoted.

Set Crane Format Style "None".
Crane Extraction "alias_phantom_param_before_promoted" AliasPhantomParamBeforePromoted.
