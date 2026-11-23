(** Found by Ephyra (round 19). A method whose receiver is not its first
    argument ([sf4 (c : bool) (t : tree)] in the eponymous module [Tree]),
    returning a closed [fold_left] whose step returns the partial
    application [f2 [7]].

    Fixed: neither [c] nor [t] is read, so both binders are named apart as
    [_x] and [_x0], and the eta-expansion of [f2 [7]] names its own
    parameter [_x0] as well.  Substituting the receiver by [*this] was not
    capture-avoiding: it rewrote the lambda's read of its parameter, which
    then printed unnamed, and the closure's [*this] became the receiver's
    copy [_self_val] ("use of undeclared identifier '_self_val'"), declared
    after the hoisted static that read it.  The substitution now stops at a
    lambda binding the same name.  Expected [t_1 = 4]. *)
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
