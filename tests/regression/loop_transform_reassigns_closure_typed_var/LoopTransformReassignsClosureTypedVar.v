(* The loop transform gives a varying shadow variable its parameter's type
   verbatim.  For a callable parameter that is a deduced template parameter --
   the caller's closure type -- those two facts contradict each other: a shadow
   exists only because the back edge reassigns it, and a closure type has
   exactly one value.

     template <typename T1, typename F0>
       requires std::is_invocable_r_v<T1, F0 &, A &>
     Lst<T1> map_In(F0 &&f) const {
       ...
       F0 _loop_f = f;                        // the caller's closure type
       while (true) {
         ...
         _loop_f = [=](const A &y) mutable {  // a different closure type
           return _loop_f(y);
         };

     error: no viable overloaded '='

   The callable is rebuilt at all because [mem x l] mentions [l]: at the
   recursive call the membership hypothesis has to be re-abstracted for the
   tail, and since the proof erases, what survives extraction is a fresh
   [A -> B] closure wrapping the old one rather than [f] passed through.

   Two ingredients are load-bearing.  The list must be an extracted inductive
   and not the [Mapping.Std] one: over [List] the same source comes out as a
   free recursive function with a [std::function] parameter and no loop at all.
   And the entry point must not itself be a method on that inductive, because a
   method on a class template is never instantiated unless something concrete
   calls it -- with [run] attached, the same defective header is emitted and the
   file compiles clean.  [run] takes a [unit] to keep Crane from attaching it.

   Reduced from Vellvm's ListUtil.map_In (rocq/Utils/ListUtil.v:140). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Inductive lst (A : Type) : Type := nil | cons (x : A) (xs : lst A).
Arguments nil {A}.
Arguments cons {A}.

Fixpoint mem {A} (x : A) (l : lst A) : Prop :=
  match l with nil => False | cons y ys => y = x \/ mem x ys end.

(** The callable takes a membership proof, so the recursive call cannot pass it
    through unchanged. *)
Definition map_In {A B : Type} (l : lst A) (f : forall (x : A), mem x l -> B)
  : lst B.
Proof.
  induction l.
  - exact nil.
  - refine (cons (f x _) (IHl _)).
    + simpl. auto.
    + intros y H. apply (f y). simpl. auto.
Defined.

Definition go (n : nat) (l : lst nat) : lst nat := map_In l (fun x _ => x + n).

(** Takes a [unit] so that Crane leaves it a free function and something
    concrete instantiates [map_In]. *)
Definition run (u : unit) : lst nat := go 3 (cons 1 (cons 2 nil)).

Crane Extraction "loop_transform_reassigns_closure_typed_var" run.
