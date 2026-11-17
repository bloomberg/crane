From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Reuse.
Set Crane NonAtomicRc.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Reuse and NonAtomicRc, a local fixpoint whose list parameter is taken
    by value matches on a field of a [const auto &] structured binding with
    [a0.v_mut()]: "'this' argument to member function 'v_mut' has type 'const
    tree', but function is not marked const".  Either flag alone is fine. *)
Module ReuseNonatomicConstVMut.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition t : nat :=
  (fun w : list bool => fold_left (fun (a : nat) (e : bool) => a + (if e then 1 else 2)) w 1)
  (let fix go (l : list tree) (acc : list bool) {struct l} : list bool :=
    match l with
    | [] => []
    | e :: r => go r (match e with
                      | Leaf => if fold_left (fun (a : bool) (_ : nat) => true) [] true then acc else []
                      | Node _ _ _ => acc
                      end)
    end in go [] []).

End ReuseNonatomicConstVMut.

Crane Extraction "reuse_nonatomic_const_v_mut" ReuseNonatomicConstVMut.
