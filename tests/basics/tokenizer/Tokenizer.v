(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Structures.Equalities.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import External.StringViewStd.
From Crane Require Import Monads.ITree Monads.IO.
From Crane Require Import External.Vector.

Import ListNotations.
Import MonadNotations.

Module ToString.

Definition pair_to_string {A B : Type} (p1 : A -> string) (p2 : B -> string) (x : A * B) : string :=
  match x with
  | (a, b) => cat "(" (cat (p1 a) (cat ", " (cat (p2 b) ")")))
  end.

Fixpoint intersperse {A : Type} (p : A -> string) (sep : string) (l : list A) : string :=
  match l with
  | nil => ""
  | cons z nil => cat sep (p z)
  | cons z l' => cat sep (cat (p z) (intersperse p sep l'))
  end.

Definition list_to_string {A : Type} (p : A -> string) (l : list A) : string :=
  match l with
  | nil => "[]"
  | cons y nil => cat "[" (cat (p y) "]")
  | cons y l' => cat "[" (cat (p y) (cat (intersperse p "; " l') "]"))
  end.

End ToString.

Module Tokenizer.

  Open Scope int63.

  Definition next_token (input soft hard : string_view) : option string_view * string_view :=
    (fix aux (fuel : nat) (index : int) (s : string_view) :=
     if eqb (length s) 0 then (None, empty_sv) else
     match fuel with
      | O => (Some s, empty_sv)
      | S fuel' =>
        let c := sv_get s index in
        if contains hard c then
          (Some (substr s 0 index), substr s (add index 1) (sub (length input) (add index 1)))
        else if contains soft c then
          if eqb index 0
          then aux fuel' 0 (substr s 1 (sub (length input) 1))
          else (Some (substr s 0 index), substr s (add index 1) (sub (length input) (add index 1)))
        else aux fuel' (add index 1) s
      end) (nat_of_int (length input)) 0 input.

  Definition list_tokens (input soft hard : string_view) : list string_view :=
    (fix aux (fuel : nat) rest :=
     match fuel with
      | O => []
      | S fuel' =>
        let t := next_token rest soft hard in
        match fst t with
        | None => []
        | Some t' => t' :: aux fuel' (snd t)
        end
      end) (nat_of_int (length input)) input.


  Fixpoint list_to_vec_h {A : Type} (l : list A) : IO (vector A) :=
    match l with
    | [] => emptyVec A
    | a :: l' =>
      v <- list_to_vec_h l' ;;
      push v a ;;
      Ret v
  end.

  Definition list_to_vec {A : Type} (l : list A) : IO (vector A) := list_to_vec_h (rev l).

  Fixpoint list_to_vec_map_h {A B : Type} (f : A -> B) (l : list A) : IO (vector B) :=
    match l with
    | [] => emptyVec B
    | a :: l' =>
      v <- list_to_vec_map_h f l' ;;
      push v (f a) ;;
      Ret v
  end.

  Definition list_to_vec_map {A B : Type} (f : A -> B) (l : list A) : IO (vector B) := list_to_vec_map_h f (rev l).

End Tokenizer.

Module Tokenizer_Properties.

  Import Tokenizer.
  Open Scope int63.

  (* ================================================================== *)
  (* Theorems about next_token                                          *)
  (* ================================================================== *)

  (* Theorem: next_token on empty input returns None *)
  Theorem next_token_empty_input :
    forall input soft hard,
      length input = 0 ->
      fst (next_token input soft hard) = None.
  Proof.
    intros input soft hard Hlen.
    unfold next_token. rewrite Hlen. rewrite nat_of_int_0. rewrite Hlen. simpl. reflexivity.
  Qed.

  (* Theorem: if next_token finds a hard delimiter at position 0,
     it returns the empty prefix *)
  Theorem next_token_leading_hard_delim :
    forall input soft hard,
      eqb (length input) 0 = false ->
      contains hard (sv_get input 0) = true ->
      fst (next_token input soft hard) = Some (substr input 0 0).
  Proof.
    intros input soft hard Hnonempty Hhard.
    unfold next_token.
    destruct (nat_of_int_pos (length input) Hnonempty) as [m Hm].
    rewrite Hm. simpl. rewrite Hnonempty. rewrite Hhard. simpl. reflexivity.
  Qed.

  (* Theorem: if next_token finds a soft delimiter at position 0 and
     the rest is empty, it returns None *)
  Theorem next_token_leading_soft_delim :
    forall input soft hard,
      eqb (length input) 0 = false ->
      contains hard (sv_get input 0) = false ->
      contains soft (sv_get input 0) = true ->
      eqb (length (substr input 1 (sub (length input) 1))) 0 = true ->
      fst (next_token input soft hard) = None.
  Proof.
    intros input soft hard Hnonempty Hnohard Hsoft Hrestlen.
    unfold next_token.
    destruct (nat_of_int_pos (length input) Hnonempty) as [m Hm].
    rewrite Hm. simpl. rewrite Hnonempty. rewrite Hnohard. rewrite Hsoft.
    destruct m; simpl; rewrite Hrestlen; reflexivity.
  Qed.

End Tokenizer_Properties.

From Crane Require Extraction.
From Crane Require Mapping.Std.

Crane Extraction "tokenizer" ToString Tokenizer.

(* TODO: most common traits in BDE
         which monads needed most to make our code BDE *)
