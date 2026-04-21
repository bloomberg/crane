From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module TailrecReorderProbe.

(** Custom list to control exact code generation. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

(** Tail-recursive reverse via accumulator.

    BUG HYPOTHESIS: When loopified, the assignments to loop variables
    [l := t] and [acc := mycons h acc] must happen in the right order.
    If [l := t] fires first, the old list node may be freed (when
    use_count drops to 0), making [h] a dangling reference in the
    subsequent [mycons h acc] construction.

    This is a potential evaluation-order / use-after-free bug in the
    loopify pass. *)
Fixpoint my_rev_append {A : Type} (l acc : mylist A) : mylist A :=
  match l with
  | mynil => acc
  | mycons h t => my_rev_append t (mycons h acc)
  end.

Definition my_reverse {A : Type} (l : mylist A) : mylist A :=
  my_rev_append l mynil.

(** Variant: TWO arguments depend on pattern-matched fields.
    [l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2]
    Both acc1 and acc2 need [h] from the OLD [l]. *)
Fixpoint dual_accum (l : mylist nat) (acc1 acc2 : mylist nat)
  : mylist nat * mylist nat :=
  match l with
  | mynil => (acc1, acc2)
  | mycons h t => dual_accum t (mycons h acc1) (mycons (h + 1) acc2)
  end.

Fixpoint mylist_sum {A : Type} (f : A -> nat) (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons h t => f h + mylist_sum f t
  end.

Definition test_rev : nat :=
  mylist_sum (fun x => x) (my_reverse (mycons 1 (mycons 2 (mycons 3 mynil)))).

Definition test_dual : nat :=
  let '(a, b) := dual_accum (mycons 10 (mycons 20 (mycons 30 mynil))) mynil mynil in
  mylist_sum (fun x => x) a + mylist_sum (fun x => x) b.

(** Tail-recursive function where the recursive argument is a COMPLEX
    expression involving multiple pattern variables. *)
Fixpoint weave (l1 l2 : mylist nat) (acc : mylist nat) : mylist nat :=
  match l1 with
  | mynil => my_rev_append acc l2
  | mycons h1 t1 =>
    match l2 with
    | mynil => my_rev_append acc l1
    | mycons h2 t2 => weave t1 t2 (mycons h2 (mycons h1 acc))
    end
  end.

Definition test_weave : nat :=
  mylist_sum (fun x => x) (weave (mycons 1 (mycons 3 mynil)) (mycons 2 (mycons 4 mynil)) mynil).

End TailrecReorderProbe.

Crane Extraction "tailrec_reorder_probe" TailrecReorderProbe.
