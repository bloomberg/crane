(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tests for pattern matching in monadic context.
    Targets match on custom inductives, nested matches, and
    match arms with effects. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

(** A simple custom inductive for testing *)
Inductive color := Red | Green | Blue.

(** A parameterized inductive *)
Inductive tree (A : Type) :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Module MatchMonadic.

(** 1. Match on custom inductive with effects in each arm *)
Definition color_name (c : color) : itree ioE string :=
  match c with
  | Red => print_endline "red" ;; Ret "red"
  | Green => print_endline "green" ;; Ret "green"
  | Blue => print_endline "blue" ;; Ret "blue"
  end.

(** 2. Match on bool inside a bind chain *)
Definition conditional_read (b : bool) : itree ioE string :=
  if b then
    line <- get_line ;;
    Ret (cat "got: " line)
  else
    Ret "skipped".

(** 3. Nested match: match on result of another match *)
Definition nested_match (n : nat) (b : bool) : itree ioE string :=
  let label := match n with
    | O => "zero"
    | S O => "one"
    | S (S _) => "many"
    end in
  if b
  then (print_endline label ;; Ret label)
  else Ret "ignored".

(** 4. Match on option in monadic context *)
Definition handle_option (o : option nat) : itree ioE nat :=
  match o with
  | Some n => print_endline "found" ;; Ret n
  | None => print_endline "missing" ;; Ret 0
  end.

(** 5. Recursive function matching on tree *)
Fixpoint tree_sum (t : tree nat) : itree ioE nat :=
  match t with
  | Leaf => Ret 0
  | Node l v r =>
    print_endline "visiting" ;;
    sl <- tree_sum l ;;
    sr <- tree_sum r ;;
    Ret (sl + v + sr)
  end.

(** 6. Match result used in bind *)
Definition match_then_bind (n : nat) : itree ioE string :=
  let tag := match n with
    | O => "A"
    | _ => "B"
    end in
  line <- get_line ;;
  Ret (cat tag line).

(** 7. Match inside a bind continuation *)
Definition bind_then_match : itree ioE int :=
  line <- get_line ;;
  let len := PrimString.length line in
  if PrimInt63.eqb len 0 then
    print_endline "empty" ;; Ret 0%int63
  else
    Ret len.

(** 8. Multiple matches in sequence *)
Definition multi_match (a b : bool) : itree ioE string :=
  let x := if a then "A" else "a" in
  let y := if b then "B" else "b" in
  print_endline (cat x y) ;;
  Ret (cat x y).

End MatchMonadic.

Crane Extraction "match_monadic" MatchMonadic.
