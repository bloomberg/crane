(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A parameter a loopified function passes unchanged to its recursive call
    is a loop invariant of the frame machine.  Its moves are dropped where
    the machine may read it again, and kept on the final path, the one
    branch that recurses no further, when nothing reads it after that:

    - [thread_end]: one non-tail call per path; the buffer is consumed only
      at the end of the input, so it is moved there, and copied nowhere.
    - [thread_both]: the same, but the result also reads the buffer after
      the recursive call returns, so the final path must copy.
    - [thread_tree]: two recursive calls, so the final path runs once per
      leaf and must copy each time. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.

Definition support : string := "loopify_final_move_support.h".

Axiom Buffer : Type.
Axiom buffer_empty : Buffer.
Axiom buffer_push : Buffer -> nat -> Buffer.
Axiom buffer_size : Buffer -> nat.

#[export] Instance buffer_mapping : TypeMapping Buffer :=
  {| type_headers := [support];
     type_cpp := Crane.Cpp.Name "final_move_support::buffer";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews Buffer;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buffer_empty_mapping : OperationMapping (Ref buffer_empty) :=
  {| operation_headers := [support];
     operation_cpp := Expr "final_move_support::buffer{}";
     operation_contract := PureOperation [] ReturnValue [] |}.

#[export] Instance buffer_push_mapping : OperationMapping (Ref buffer_push) :=
  {| operation_headers := [support];
     operation_cpp := Expr "final_move_support::push(%arg(b), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Take |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance buffer_size_mapping : OperationMapping (Ref buffer_size) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<std::uint64_t>(%arg(b).items.size())";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

Inductive tree : Type :=
| Leaf : nat -> tree
| Node : tree -> tree -> tree.

Module LoopifyFinalMove.

Fixpoint thread_end (b : Buffer) (k : nat) : Buffer * nat :=
  match k with
  | O => (buffer_push b 7, 0)
  | S k' => let (b', n) := thread_end b k' in (b', k + n)
  end.

Fixpoint thread_both (b : Buffer) (k : nat) : Buffer * nat :=
  match k with
  | O => (buffer_push b 7, 0)
  | S k' => let (b', n) := thread_both b k' in (b', k + n + buffer_size b)
  end.

Fixpoint thread_tree (b : Buffer) (t : tree) : list Buffer :=
  match t with
  | Leaf x => [buffer_push b x]
  | Node l r => thread_tree b l ++ thread_tree b r
  end.

End LoopifyFinalMove.

Set Crane Loopify.
Crane Extraction "loopify_final_move" LoopifyFinalMove.
