(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An interpreter for a small imperative language whose variables live in
    an ST array.  [exec] runs a statement and returns the number of steps
    it took.

    It needs general recursion, written with ITree's [rec] and [call]
    ([callE]): a [While] may run forever, so [exec] has no termination
    argument (it is neither structural nor on a measure), and it is not
    tail recursive -- [Seq] runs its first statement and then its second,
    [While] its body and then the loop again, adding up their steps -- so a
    [CoFixpoint] would not do either: the guard condition rejects a
    recursive call on the left of a bind. *)

From Stdlib Require Import Arith.PeanoNat List.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.STMonad
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Inductive expr : Type :=
| Num (n : nat)
| Var (x : nat)
| Add (a b : expr)
| Sub (a b : expr)
| Mul (a b : expr)
| Lt (a b : expr).

Inductive stmt : Type :=
| Skip
| Assign (x : nat) (e : expr)
| Seq (s1 s2 : stmt)
| If (c : expr) (s1 s2 : stmt)
| While (c : expr) (body : stmt).

Section Imp.

  Context {R : STRefs}.
  Notation V := (fun _ : nat => nat).
  Notation E0 := (STEvent R V +' exceptE Err).
  Notation E1 := (callE stmt nat +' E0).

  (** The value of [e], the variables read from [vars]. *)
  Fixpoint eval (vars : STArray nat) (e : expr) : itree E1 nat :=
    match e with
    | Num n => Ret n
    | Var x => readArray (E := E1) (V := V) vars x
    | Add a b => x <- eval vars a;; y <- eval vars b;; Ret (x + y)
    | Sub a b => x <- eval vars a;; y <- eval vars b;; Ret (x - y)
    | Mul a b => x <- eval vars a;; y <- eval vars b;; Ret (x * y)
    | Lt a b => x <- eval vars a;; y <- eval vars b;; Ret (if Nat.ltb x y then 1 else 0)
    end.

  (** One statement: its substatements are run by [call]. *)
  Definition exec_body (vars : STArray nat) (s : stmt) : itree E1 nat :=
    match s with
    | Skip => Ret 1
    | Assign x e =>
      v <- eval vars e;;
      writeArray (E := E1) (V := V) vars x v;;
      Ret 1
    | Seq s1 s2 =>
      n1 <- call s1;;
      n2 <- call s2;;
      Ret (n1 + n2)
    | If c s1 s2 =>
      v <- eval vars c;;
      n <- (if Nat.eqb v 0 then call s2 else call s1);;
      Ret (S n)
    | While c body =>
      v <- eval vars c;;
      if Nat.eqb v 0 then Ret 1
      else
        n1 <- call body;;
        n2 <- call (While c body);;
        Ret (S (n1 + n2))
    end.

  Definition exec (vars : STArray nat) (s : stmt) : itree E0 nat :=
    rec (exec_body vars) s.

  (** Runs [s] on [n] variables, all [0]: the steps it took and the final
      variables. *)
  Definition run (n : nat) (s : stmt) : itree E0 (nat * list nat) :=
    vars <- newArray (E := E0) (V := V) n 0;;
    steps <- exec vars s;;
    vs <- getElems (E := E0) (V := V) vars;;
    Ret (steps, vs).

End Imp.

(** [x1 := k!], counting [x0] down from [k]. *)
Definition factorial (k : nat) : stmt :=
  Seq (Assign 0 (Num k))
  (Seq (Assign 1 (Num 1))
  (While (Lt (Num 0) (Var 0))
     (Seq (Assign 1 (Mul (Var 1) (Var 0)))
          (Assign 0 (Sub (Var 0) (Num 1)))))).

(** [x1 := fib k], counting [x0] down from [k] with [(x1, x2) := (x2, x1 + x2)]. *)
Definition fibonacci (k : nat) : stmt :=
  Seq (Assign 0 (Num k))
  (Seq (Assign 1 (Num 0))
  (Seq (Assign 2 (Num 1))
  (While (Lt (Num 0) (Var 0))
     (Seq (Assign 3 (Add (Var 1) (Var 2)))
     (Seq (Assign 1 (Var 2))
     (Seq (Assign 2 (Var 3))
          (Assign 0 (Sub (Var 0) (Num 1))))))))).

(** A nested loop: [x2 := k * k], one increment at a time. *)
Definition square (k : nat) : stmt :=
  Seq (Assign 0 (Num k))
  (While (Lt (Num 0) (Var 0))
     (Seq (Assign 1 (Num k))
     (Seq (While (Lt (Num 0) (Var 1))
             (Seq (Assign 2 (Add (Var 2) (Num 1)))
                  (Assign 1 (Sub (Var 1) (Num 1)))))
          (Assign 0 (Sub (Var 0) (Num 1)))))).

(** Never terminates: [exec] accepts it all the same.  Not run. *)
Definition forever : stmt := While (Num 1) (Assign 0 (Add (Var 0) (Num 1))).

(** In the model: [runST] interprets [rec] with ITree's [mrec]. *)
Transparent HAList.halist_lookup HAList.halist_add HAList.HMap_halist HAList.HMapOk_halist.

Lemma factorial_5 :
  burn 5000 (ITree.map snd (runST (fun R => run (R := R) 2 (factorial 5)))) = Ret [0; 120].
Proof. lazy. reflexivity. Qed.

Lemma square_3 :
  burn 5000 (ITree.map snd (runST (fun R => run (R := R) 3 (square 3)))) = Ret [0; 0; 9].
Proof. lazy. reflexivity. Qed.

Module ImpWhile.
  Definition run_factorial (k : nat) : nat * list nat := run_st (run (R := cpp_refs) 2 (factorial k)).
  Definition run_fibonacci (k : nat) : nat * list nat := run_st (run (R := cpp_refs) 4 (fibonacci k)).
  Definition run_square (k : nat) : nat * list nat := run_st (run (R := cpp_refs) 3 (square k)).
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End ImpWhile.

Crane Extraction "imp_while" ImpWhile.
