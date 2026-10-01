(** Crane bug (extraction anomaly): under [Set Crane Loopify], a function
    parameterised by a class whose body let-binds a local [fix] calling back
    into it failed with [Anomaly "Uncaught exception Failure("nth")."].

    The local fixpoint is adopted as a second entry of the function's
    machine.  Its captures are carried in the entry's frame, and it named the
    class dictionary's template parameter ([_tcI0], mentioned by the call
    [_tcI0::size(...)]) as one.  No type is known for that name, so the
    adoption was abandoned -- after the calls into the fixpoint had already
    been routed to entry 1, which an abandoned adoption never registers.

    Reduced from Vellvm, [Semantics/MemoryBytes.v:112]
    ([dvalue_extract_byte], in a section over the memory parameters, with
    two local [fix loop]s calling it back). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module LoopifyFixCapturesClassParam.
  Class Sized := { size : nat -> nat }.

  Inductive tree : Type := Leaf (n : nat) | Node (ts : list tree).

  Section S.
    Context `{Sized}.
    Fixpoint f (t : tree) (i : nat) {struct t} : option nat :=
      let bytes :=
        fix loop (ts : list tree) (k : nat) {struct ts} :=
          match ts with
          | [] => None
          | t' :: ts' => if Nat.ltb k (size 2) then f t' k else loop ts' (k - size 2)
          end in
      match t with
      | Leaf n => Some (n + i)
      | Node ts => bytes ts i
      end.
  End S.

  #[local] Instance id_size : Sized := { size n := n }.

  (* loop [Leaf 1; Node [Leaf 5]] 3 skips the leaf, enters the node at 1,
     and reaches Leaf 5 at 1. *)
  Definition result : option nat := f (Node [Leaf 1; Node [Leaf 5]]) 3.
End LoopifyFixCapturesClassParam.

Set Crane Loopify.
Crane Extraction "loopify_fix_captures_class_param" LoopifyFixCapturesClassParam.
