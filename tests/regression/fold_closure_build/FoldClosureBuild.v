From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module FoldClosureBuild.

(** FOLD-BASED CLOSURE BUILDING

    BUG HYPOTHESIS: When a fold_left uses its accumulator function
    parameter to build closures, the closure for each iteration
    captures the fold's function parameter by [&]. If the fold
    function is inlined and the parameter dies after the fold
    call returns, the closures hold dangling references.

    This is different from existing wip tests because:
    1. The closures are built INSIDE A FOLD, not in a direct recursive function
    2. The fold CALLBACK captures pattern variables from the fold's
       own match expression, creating a nested scope issue
    3. Multiple closures are chained through the fold, each
       depending on the previous one *)

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

(** Simple fold_left. *)
Fixpoint fold_left {A B : Type} (f : A -> B -> A) (acc : A) (l : mylist B) : A :=
  match l with
  | mynil => acc
  | mycons h t => fold_left f (f acc h) t
  end.

(** Pattern 1: Build a COMPOSED function via fold.
    Each step wraps the accumulator in a new closure.

    Equivalent to:
    compose_all [10, 20, 30] id
    = fold_left (fun acc h => fun x => acc(h + x)) id [10,20,30]
    = fun x => id(10 + (20 + (30 + x)))
    = fun x => 60 + x

    The inner closure [fun x => acc(h+x)] captures acc (std::function)
    and h (unsigned int). If these are captured by [=], safe. By [&], dangles. *)
Definition compose_adders (l : mylist nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (h : nat) => fun x => acc (h + x))
            (fun x => x)
            l.

(** test1: compose_adders [10,20,30] 7 = 67 *)
Definition test1 : nat := compose_adders (mycons 10 (mycons 20 (mycons 30 mynil))) 7.

(** Pattern 2: Store the composed function and call it TWICE.
    If the closure chain has dangling references, the second call
    might read clobbered stack memory. *)
Definition test2 : nat :=
  let f := compose_adders (mycons 5 (mycons 10 mynil)) in
  f 0 + f 100.

(** Pattern 3: Fold producing a list of closures (not composing them).
    Each closure captures the list element from the fold iteration. *)
Definition collect_adders (l : mylist nat) : mylist (nat -> nat) :=
  fold_left (fun (acc : mylist (nat -> nat)) (h : nat) =>
    mycons (fun x => h + x) acc)
    mynil
    l.

Fixpoint apply_all (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f rest => f x + apply_all rest x
  end.

(** test3: collect_adders [10,20,30]
    = [(30+_), (20+_), (10+_)]  (reversed by fold_left)
    apply_all with x=5: (30+5) + (20+5) + (10+5) = 75 *)
Definition test3 : nat :=
  apply_all (collect_adders (mycons 10 (mycons 20 (mycons 30 mynil)))) 5.

(** Pattern 4: Fold with a FIXPOINT as accumulator.
    The fixpoint captures both acc and h from the fold callback.

    BUG HYPOTHESIS: The fixpoint [go] uses [&] to capture acc and h.
    [acc] is the std::function accumulator from fold_left.
    [h] is the current list element.
    Both are locals in the fold callback's scope.
    When fold returns, these scopes are destroyed, but the
    final fixpoint (stored in the accumulator) still references them. *)
Definition compose_with_fix (l : mylist nat) : nat -> nat :=
  fold_left (fun (acc : nat -> nat) (h : nat) =>
    let fix go (x : nat) : nat :=
      match x with
      | O => acc h
      | S x' => S (go x')
      end
    in go)
    (fun x => x)
    l.

(** test4: compose_with_fix [10]
    first iteration: acc=id, h=10
    go(x) = x + acc(h) = x + id(10) = x + 10
    test4 = go(5) = 5 + 10 = 15 *)
Definition test4 : nat := compose_with_fix (mycons 10 mynil) 5.

(** test5: compose_with_fix [10, 20]
    first: acc=id, h=10, go1(x) = x + id(10) = x + 10
    second: acc=go1, h=20, go2(x) = x + go1(20) = x + 30
    test5 = go2(7) = 7 + 30 = 37 *)
Definition test5 : nat := compose_with_fix (mycons 10 (mycons 20 mynil)) 7.

End FoldClosureBuild.

Crane Extraction "fold_closure_build" FoldClosureBuild.
