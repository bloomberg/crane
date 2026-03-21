From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListGenerators.

(* List generation and iteration functions *)

(* Cycle list n times *)
Fixpoint cycle_fuel (fuel : nat) (n : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match n with
    | 0 => []
    | S n' =>
      match l with
      | [] => []
      | _ => app l (cycle_fuel fuel' n' l)
      end
    end
  end.

Definition cycle (n : nat) (l : list nat) : list nat :=
  cycle_fuel (n * length l) n l.

(* Iterate function n times *)
Fixpoint iterate (f : nat -> nat) (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: iterate f n' (f x)
  end.

(* Build list by applying function to indices *)
Fixpoint build_list_aux (n idx : nat) (f : nat -> nat) : list nat :=
  match n with
  | 0 => []
  | S n' => f idx :: build_list_aux n' (idx + 1) f
  end.

Definition build_list (n : nat) (f : nat -> nat) : list nat :=
  build_list_aux n 0 f.

(* Initialize list with function *)
Fixpoint init_list (n : nat) (f : nat -> nat) : list nat :=
  match n with
  | 0 => []
  | S n' => f 0 :: (fix go i :=
    match i with
    | 0 => []
    | S i' => f (n - i) :: go i'
    end) n'
  end.

(* Range of numbers *)
Fixpoint range (start count : nat) : list nat :=
  match count with
  | 0 => []
  | S count' => start :: range (start + 1) count'
  end.

(* Replicate element n times *)
Fixpoint replicate_elem (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: replicate_elem n' x
  end.

(* Replicate each element n times *)
Fixpoint replicate_each (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    let reps := replicate_elem n x in
    app reps (replicate_each n xs)
  end.

(* Tabulate - like build_list but clearer name *)
Fixpoint tabulate (n : nat) (f : nat -> nat) : list nat :=
  match n with
  | 0 => []
  | S n' => (fix aux idx :=
    match idx with
    | 0 => [f 0]
    | S idx' => app (aux idx') [f idx]
    end) n'
  end.

(* Zip with function *)
Fixpoint zip_with (f : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  end.

(* Enumeration - pair each element with its index *)
Fixpoint enumerate_aux (idx : nat) (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | x :: xs => (idx, x) :: enumerate_aux (idx + 1) xs
  end.

Definition enumerate (l : list nat) : list (nat * nat) :=
  enumerate_aux 0 l.

End LoopifyListGenerators.

Set Crane Loopify.
Crane Extraction "loopify_list_generators" LoopifyListGenerators.
