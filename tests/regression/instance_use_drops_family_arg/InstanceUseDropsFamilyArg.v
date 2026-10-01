(** Crane bug: a use of an instance parametric over a family (fixed as a
    [template <typename T1> struct Monad_box] in 0b2cfbbd5) names the
    instance without its family argument.

    Observed:
      template <typename T1>
      static box<AllE<T1, std::any>, Nat> incr(const Nat &n) {
        return bind<Monad_box, Nat, Nat>(ret<Monad_box, Nat>(n), [](Nat m) {
          return ret<Monad_box, Nat>(Nat::s(m)); });
    It should be [Monad_box<AllE<T1, std::any>>].  Diagnostic:
      error: no matching function for call to 'ret'
      (Vellvm: "candidate template ignored: invalid explicitly-specified
       argument for template parameter '_tcI0'")

    The family here is an alias over a section variable ([AllE] under
    [Context {P : Type}]), as in Vellvm, where the events are
    [CFGEtop := CallE +' ...] inside the [Params] section and code runs in
    [CFGtop := itree CFGEtop].  (instance_family_param's use at a closed
    family, [box noE], passes.)

    Reduced from Vellvm, [Semantics/Libraries.v] ([i8_str_index]'s
    [ITree.iter] body [ret (inl ...)]), emitted as
    [Monad0::template ret<Monad_itree, ...>] (30 errors). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module InstanceUseDropsFamilyArg.
  Class Monad (M : Type -> Type) : Type :=
    { ret : forall {A : Type}, A -> M A
    ; bind : forall {A B : Type}, M A -> (A -> M B) -> M B }.

  Inductive box (E : Type -> Type) (A : Type) : Type := Box (a : A).
  Arguments Box {E A}.

  #[global] Instance Monad_box {E : Type -> Type} : Monad (box E) :=
    { ret := fun A a => Box a
    ; bind := fun A B m k => match m with Box a => k a end }.

  Section WithParam.
    Context {P : Type}.
    Variant aE : Type -> Type := A : P -> aE nat.
    Variant bE : Type -> Type := B : bE unit.
    (* Vellvm: [CFGEtop := CallE +' ...] inside a section over [Params],
       and code in [CFGtop := itree CFGEtop] using the itree monad. *)
    Definition AllE : Type -> Type := fun X => sum (aE X) (bE X).
    Definition top (X : Type) : Type := box AllE X.

    Definition incr (n : nat) : box AllE nat := bind (ret n) (fun m => ret (S m)).
  End WithParam.

  Definition r : box (@AllE nat) nat := @incr nat 2.
  Definition is_three : bool := match r with Box n => Nat.eqb n 3 end.
End InstanceUseDropsFamilyArg.

Crane Extraction "instance_use_drops_family_arg" InstanceUseDropsFamilyArg.
