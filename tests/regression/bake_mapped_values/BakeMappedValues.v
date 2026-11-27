(** [Crane Bake] of values whose types are typed-mapped C++ types, and of a
    deep value whose recursive field comes first.

    [Mapping.Std] maps [PrimArray.array] to [persistent_array], [option] to
    [std::optional], [prod] to [std::pair], [PrimString.string] to
    [std::string], [PrimInt63.int] to [int64_t] and [PrimFloat.float] to
    [double]; [Mapping.DequeList] maps [list] to [std::deque].  Each is
    written and read back by the image's generic hooks (a sequence container,
    an optional, a pair, a string).  [deep] is a left spine of 30000 nodes:
    writing and reading it walks the spine with an explicit stack, whichever
    field holds it. *)
From Crane Require Import Mapping.NatInt Mapping.Std Mapping.DequeList.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimInt63 PrimFloat PrimArray PrimString.
Import ListNotations.

Set Crane Loopify.

Module BakeMappedValues.

Definition arr : PrimArray.array nat := PrimArray.set (PrimArray.make 4%uint63 7) 1%uint63 9.

Definition labelled : option (PrimString.string * nat) := Some ("label"%pstring, 3).

Definition digits : list nat := [3; 1; 4; 1; 5].

Definition word : PrimInt63.int := 42%uint63.

Definition half : PrimFloat.float := 0.5%float.

Inductive spine : Type := Root | Grow (rest : spine) (x : nat).

Definition deep : spine := Nat.iter 30000 (fun s => Grow s 1) Root.

Fixpoint weight (s : spine) : nat := match s with Root => 0 | Grow r x => x + weight r end.

Definition arr_sum : nat :=
  PrimArray.get arr 0%uint63 + PrimArray.get arr 1%uint63 + PrimArray.get arr 9%uint63.

Definition label_length : nat :=
  match labelled with Some (s, n) => if PrimInt63.eqb (PrimString.length s) 5%uint63 then n + 5 else n | None => 0 end.

Definition digits_sum : nat := fold_left Nat.add digits 0.

Definition deep_weight : nat := weight deep.

End BakeMappedValues.

Crane Bake BakeMappedValues.arr BakeMappedValues.labelled BakeMappedValues.digits
  BakeMappedValues.word BakeMappedValues.half BakeMappedValues.deep.

Crane Extraction "bake_mapped_values" BakeMappedValues.
