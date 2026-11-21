(** Found by Ephyra (round 19). A method whose receiver is not its first
    argument ([sf4 (c : bool) (t : tree)] in the eponymous module [Tree]),
    returning a closed [fold_left] whose step returns the partial
    application [f2 [7]].

    Expected: compiles, and [t_1 = 4] ([f2 [7] 3 = 1 + 3]).

    Actual: compile error "use of undeclared identifier '_self_val'". The
    closed fold is hoisted to a function-local [static const] built once
    ("Built on the first call and immortal"), and the eta-expanded partial
    application inside it is printed as [[=](uint64_t) -> uint64_t { return
    f2(_pa0, _self_val); }]: the lambda's own parameter is left unnamed and
    its use is spelled as the receiver's copy [_self_val], which is declared
    only after the static (and could not be captured by it anyway). With
    the receiver first, or with a fold that is not closed (so not hoisted),
    it compiles. Also on main. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module MethodHoistedEtaSelfVal.
Module Tree.
Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).
Definition f2 (a : list nat) (b : nat) : nat := List.length a + b.
Definition sf4 (c : bool) (t : tree) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (e : bool) => f2 [7]) [true] (fun _ : nat => 0).
End Tree.
Definition t_1 : nat := Tree.sf4 true Tree.Leaf 3.
End MethodHoistedEtaSelfVal.
Eval vm_compute in MethodHoistedEtaSelfVal.t_1.
Crane Extraction "method_hoisted_eta_self_val" MethodHoistedEtaSelfVal.
