(** A method hoisted onto a datatype struct calls a module emitted later.

    Vellvm hits this twice.  [List.list<A>::maximumByOpt] calls
    [ListUtil::option_pick_large], and [Z::Z_le_dec] calls [BinInt::compare];
    both callees are emitted thousands of lines after the struct whose member
    calls them.  Reordering cannot fix either one: [ListUtil] mentions
    [List::list] and [BinInt] mentions [Z], so the dependency is a cycle
    between the two emitted structs, created by hoisting the function into the
    type.  Crane already has the shape that solves it -- free functions are
    declared and then defined out of line -- so the missing piece is the same
    treatment for hoisted members.

    Expected: [deeper] is a member of [tree], and its body names [Helper], so
    [Helper] must be at least declared before [tree] is defined.
*)

From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith.

Inductive tree : Set := | leaf : tree | node : tree -> tree -> tree.

(* Emitted after [tree], because it mentions [tree]. *)
Module Helper.
  Definition is_leaf (t : tree) : bool :=
    match t with leaf => true | node _ _ => false end.
  Definition pick (a b : nat) : nat := if Nat.leb a b then b else a.
End Helper.

(* First argument is [tree], so this is hoisted into the [tree] struct --
   where it names [Helper::pick], which does not exist yet. *)
Fixpoint deeper (t : tree) : nat :=
  match t with
  | leaf => 0
  | node l r => S (Helper.pick (deeper l) (deeper r))
  end.

Crane Extraction "member_calls_later" deeper.
