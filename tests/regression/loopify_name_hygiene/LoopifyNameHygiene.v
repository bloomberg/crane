From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Set Crane Loopify.

(** Loopification invents C++ names -- the frame structs [_Enter] and
    [_Resume_<Ctor>], and the locals [_stack], [_result], [_self] -- without
    checking whether the Rocq source already spells them.  A program that does
    is miscompiled: the generated names capture the user's, and the loop body
    reads the frame stack where it meant to read a constant. *)

Module LoopifyNameHygiene.

  (** Constructor names that become loopify's frame structs. *)
  Inductive _Frame := _Enter : nat -> _Frame | _Resume_Cons : _Frame -> _Frame.

  Fixpoint depth (f : _Frame) : nat :=
    match f with
    | _Enter n => n
    | _Resume_Cons g => S (depth g)
    end.

  Fixpoint mk (n : nat) : _Frame :=
    match n with
    | O => _Enter 1
    | S k => _Resume_Cons (mk k)
    end.

  (** Definition names that become loopify's locals. *)
  Definition _stack : nat := 1.
  Definition _result : nat := 2.
  Definition _self : nat := 3.

  Fixpoint locals (n : nat) : nat :=
    match n with
    | O => _stack + _result + _self
    | S k => S (locals k)
    end.

  Definition run : nat := depth (mk 5) + locals 10.

End LoopifyNameHygiene.

Crane Extraction "loopify_name_hygiene" LoopifyNameHygiene.
