(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tests for closures and higher-order functions in monadic context.
    Targets lambda capture, partial application, and HOF patterns. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module MonadicClosure.

(** 1. Lambda capturing a bind result *)
Definition capture_bind : itree ioE int :=
  line <- get_line ;;
  let f := fun (_ : nat) => PrimString.length line in
  Ret (PrimInt63.add (f 0) (f 1)).

(** 2. Higher-order function taking a pure callback *)
Definition apply_after_effect {A B : Type} (f : A -> B) (m : itree ioE A) : itree ioE B :=
  x <- m ;; Ret (f x).

Definition test_apply_after : itree ioE int :=
  apply_after_effect PrimString.length get_line.

(** 3. Function returning a closure from monadic context *)
Definition make_greeter : itree ioE (string -> string) :=
  prefix <- get_line ;;
  Ret (fun name => cat prefix name).

(** 4. Passing effectful result to a HOF *)
Definition with_length (f : int -> int) : itree ioE int :=
  line <- get_line ;;
  Ret (f (PrimString.length line)).

Definition test_with_length : itree ioE int :=
  with_length (fun n => PrimInt63.add n 1).

(** 5. Nested closures over bindings *)
Definition nested_capture : itree ioE int :=
  a <- get_line ;;
  b <- get_line ;;
  let la := PrimString.length a in
  let lb := PrimString.length b in
  Ret (PrimInt63.add la lb).

(** 6. Closure used in a fold-like pattern *)
Fixpoint count_matching (pred : string -> bool) (xs : list string) : itree ioE nat :=
  match xs with
  | nil => Ret 0
  | cons x rest =>
    n <- count_matching pred rest ;;
    if pred x then Ret (S n) else Ret n
  end.

Definition test_count : itree ioE nat :=
  count_matching
    (fun s => PrimInt63.eqb (PrimString.length s) 0)
    (cons "a" (cons "" (cons "bc" nil))).

(** 7. Effect inside a let, result used later *)
Definition let_effect_capture : itree ioE int :=
  line <- get_line ;;
  let len := PrimString.length line in
  print_endline line ;;
  Ret len.

(** 8. Two closures with different captured variables *)
Definition two_closures : itree ioE (int * int) :=
  a <- get_line ;;
  b <- get_line ;;
  let la := PrimString.length a in
  let lb := PrimString.length b in
  Ret (la, lb).

End MonadicClosure.

Crane Extraction "monadic_closure" MonadicClosure.
