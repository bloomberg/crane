(** Crane bug: a constructor whose type argument is a section-local
    instance's [Type] field, built inside a lambda, spells the instance at
    [std::any] instead of the declaration's own [_tcI0]:
      MemS<typename MemoryModelStateV<std::any>::state, ...>::mub(msg)
    ([constraints not satisfied ... with _tcI0 = std::any]).

    Reduced from Vellvm, [Semantics/Implementations/Memory.v]
    [read_byte_raw]: [s <- get ;; match ... with Some b => ret b | None =>
    Mub msg end], where [memM := memS state ptr provenance]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.
From ExtLib Require Import Structures.Monad.

Module PromotedFieldCtorTargInLambda.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Class MemState {Pa : Params} : Type := { state : Type ; initial_state : state ; size_of : state -> nat }.

  Inductive memS (S X : Type) : Type :=
  | Mret : X -> memS S X
  | Mub : nat -> memS S X
  | Mget : (S -> memS S X) -> memS S X.
  Arguments Mret {S X}.
  Arguments Mub {S X}.
  Arguments Mget {S X}.

  Fixpoint memS_bind {S X Y} (c : memS S X) (k : X -> memS S Y) : memS S Y :=
    match c with
    | Mret x => k x
    | Mub n => Mub n
    | Mget g => Mget (fun s => memS_bind (g s) k)
    end.
  #[global] Instance memS_mon {S} : Monad (memS S) :=
    {| ret _ x := Mret x ; bind _ _ c k := memS_bind c k |}.
  Definition get {S} : memS S S := Mget (fun s => Mret s).

  Definition memM {Pa : Params} {MS : @MemState Pa} (A : Type) : Type := memS state A.

  Section Implementation.
    Context {Pa : Params}.
    Record St : Type := mkSt { mem : list ptr }.
    Instance StateV : @MemState Pa :=
      { state := St ; initial_state := mkSt [] ; size_of := fun s => length (mem s) }.
    (* [read_byte_raw]: the failing constructor sits in a continuation. *)
    Definition read_size (msg : nat) : memM nat :=
      @bind (memS state) memS_mon _ _ get
        (fun s => match size_of s with
                  | O => Mub msg
                  | S k => @ret (memS state) memS_mon _ k
                  end).
    Definition run (m : memS St nat) (s : St) : option nat :=
      match m with
      | Mret x => Some x
      | Mub _ => None
      | Mget k => match k s with Mret x => Some x | _ => None end
      end.
  End Implementation.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition is_zero : bool :=
    match run (read_size 3) (mkSt [1]) with Some n => Nat.eqb n 0 | None => false end.
End PromotedFieldCtorTargInLambda.

Crane Extraction "promoted_field_ctor_targ_in_lambda" PromotedFieldCtorTargInLambda.
