(* Rocq bug #13581: complex records with let-bindings in parameters,
   mutual inductives, and mutual coinductives *)

Require Crane.Extraction.

Module RocqBug13581.

Record mixin_of T0 (b : unit) (T := T0) := Mixin { mixin_f : T0 -> let U := T0 in U }.
Definition d := Mixin nat tt (fun x => x).

Record R T0 (b : nat) (c := b) (T := T0) (e : nat) (d : c = e) := Build
  { g : T0 -> let U := T0 in U ; h : d = d ; x : nat ; y := x + x }.

Definition r := {| g := (fun x : nat => x) ; h := eq_refl (eq_refl 0) ; x := 0 |}.

Inductive I T (a : T) (U := T) (b : T) (c := (a,b)) : forall d (e := S d) (h : S d = e), Type :=
| C : I T a b 0 eq_refl
| D : J T a b true eq_refl -> I T a b 1 eq_refl
with J T (a : T) (U := T) (b : T) (c := (a,b)) : forall (d : bool) (h : d = true), Type :=
| E : I T a b 0 eq_refl -> J T a b true eq_refl.

Definition c := D _ _ _ (E _ _ _ (C nat 0 0)).

End RocqBug13581.

Crane Extraction "rocq_bug_13581" RocqBug13581.
