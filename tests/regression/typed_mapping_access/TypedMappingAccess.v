(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Parameter access planning (src/core_plan/access.mli): a generated
    function's parameter of a typed-mapped type takes the physical form its
    uses require, the requirements joined across direct calls to a fixed
    point.

    - [Handle], a mutable handle passed by const reference
      ([MutableHandle HandleByConstReference], [std::shared_ptr]): reading
      and writing through it take [const T&], reseating it ([Replace])
      takes [T&], keeping it ([Take]) takes [T].
    - [Buf], a mutable value read by const reference ([MutableValue]):
      reading takes [const T&], writing it in place takes [T&], at every
      level of a chain of calls ending in the write.
    - A recursive group reaches the requirement through the partner that
      has it.
    - A function passed as a value keeps the canonical ABI: it takes a copy
      by value, which it may replace.
    - An argument that is not a variable the caller may write is
      materialised for a call that writes or replaces it in place.
    - Self recursion lowered to a loop rebinds the caller's object through
      the reference; a stack of frames holds a copy per frame.
    - Under a closure a parameter is a copy the closure holds, so the
      closure's replacement makes the parameter only read. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.
Set Crane Loopify.

Definition support : string := "typed_mapping_access_support.h".

Axiom Handle : Type.
Axiom handle_new : nat -> Handle.
Axiom handle_get : Handle -> nat.
Axiom handle_set : Handle -> nat -> Handle.
Axiom handle_reseat : Handle -> nat -> Handle.
Axiom handle_keep : Handle -> Handle.

Axiom Buf : Type.
Axiom buf_make : nat -> Buf.
Axiom buf_len : Buf -> nat.
Axiom buf_push : Buf -> nat -> Buf.

#[export] Instance handle_mapping : TypeMapping Handle :=
  {| type_headers := [support];
     type_cpp := Crane.Cpp.Name "access_support::handle";
     type_components := [];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views := NoViews Handle;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance handle_new_mapping : OperationMapping (Ref handle_new) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::make(%arg(n))";
     operation_contract :=
       EffectfulOperation [{| argument_name := "n"; argument_use := Read |}]
         (ReturnFreshIdentity []) [] |}.

#[export] Instance handle_get_mapping : OperationMapping (Ref handle_get) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::get(%arg(h))";
     operation_contract :=
       PureOperation [{| argument_name := "h"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance handle_set_mapping : OperationMapping (Ref handle_set) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::set(%arg(h), %arg(n))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "h"; argument_use := Write |};
          {| argument_name := "n"; argument_use := Read |}]
         (ReturnSameIdentity "h") [] |}.

#[export] Instance handle_reseat_mapping : OperationMapping (Ref handle_reseat) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::reseat(%arg(h), %arg(n))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "h"; argument_use := Replace |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance handle_keep_mapping : OperationMapping (Ref handle_keep) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::keep(%arg(h))";
     operation_contract :=
       PureOperation [{| argument_name := "h"; argument_use := Take |}] ReturnValue [] |}.

#[export] Instance buf_mapping : TypeMapping Buf :=
  {| type_headers := [support];
     type_cpp := Crane.Cpp.Name "access_support::buf";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := MutableValue ReadByConstReference;
     type_views := NoViews Buf;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buf_make_mapping : OperationMapping (Ref buf_make) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::buf_make(%arg(n))";
     operation_contract :=
       PureOperation [{| argument_name := "n"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance buf_len_mapping : OperationMapping (Ref buf_len) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::buf_len(%arg(b))";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance buf_push_mapping : OperationMapping (Ref buf_push) :=
  {| operation_headers := [support];
     operation_cpp := Expr "access_support::buf_push(%arg(b), %arg(x))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "b"; argument_use := Write |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

Module TypedMappingAccess.

(** Reads only: the canonical read form. *)
Definition peek (h : Handle) : nat := handle_get h.

(** Writes through the handle, two calls deep. *)
Definition poke (h : Handle) (n : nat) : Handle := handle_set h n.
Definition poke_middle (h : Handle) (n : nat) : Handle := poke h (S n).
Definition poke_outer (h : Handle) (n : nat) : nat := handle_get (poke_middle h (S n)).

(** Reseats the handle, two calls deep. *)
Definition reseat (h : Handle) (n : nat) : nat := handle_get (handle_reseat h n).
Definition reseat_outer (h : Handle) (n : nat) : nat := S (reseat h n).

(** Keeps the handle: owned, by value, even though it is reseated too. *)
Definition keep (h : Handle) : Handle := handle_keep h.
Definition keep_and_reseat (h : Handle) : nat :=
  let k := handle_keep h in
  let r := handle_get (handle_reseat h 7) in
  handle_get k + r.

(** Writes the buffer in place, two calls deep. *)
Definition buf_size (b : Buf) : nat := buf_len b.
Definition push (b : Buf) (x : nat) : Buf := buf_push b x.
Definition push_middle (b : Buf) : Buf := push b 1.
Definition push_outer (b : Buf) : nat := buf_len (push_middle b).

(** A recursive group: [ping] reseats, [pong] only passes its handle to
    [ping], and is first in the group. *)
Fixpoint pong (h : Handle) (n : nat) : nat :=
  match n with
  | O => handle_get h
  | S m => ping h m
  end
with ping (h : Handle) (n : nat) : nat :=
  match n with
  | O => handle_get (handle_reseat h 9)
  | S m => pong h m
  end.

(** [reseat_value] is passed as a value: it keeps the canonical ABI. *)
Definition apply_handle (f : Handle -> nat) (h : Handle) : nat := f h.
Definition reseat_value (h : Handle) : nat := handle_get (handle_reseat h 3).
Definition through_value (h : Handle) : nat := apply_handle reseat_value h.

(** A value that is not a variable, passed where the callee replaces or
    writes it in place, is materialised for the call. *)
Definition reseat_fresh (n : nat) : nat := reseat (handle_new n) 4.
Definition reseat_fresh_op (n : nat) : nat := handle_get (handle_reseat (handle_new n) 2).
Definition push_fresh (n : nat) : nat := push_outer (buf_make n).

(** Self recursion: in a loop, and through a stack of frames
    ([Crane Loopify] is set). *)
Fixpoint reseat_loop (h : Handle) (n : nat) : nat :=
  match n with
  | O => handle_get h
  | S m => reseat_loop (handle_reseat h n) m
  end.

Fixpoint push_loop (b : Buf) (n : nat) : nat :=
  match n with
  | O => buf_len b
  | S m => push_loop (buf_push b n) m
  end.

Fixpoint reseat_sum (h : Handle) (n : nat) : nat :=
  match n with
  | O => handle_get h
  | S m => handle_get (handle_reseat h n) + reseat_sum h m
  end.

Fixpoint reseat_each (h : Handle) (l : list nat) : nat :=
  match l with
  | [] => handle_get h
  | x :: r => reseat_each (handle_reseat h x) r
  end.

Fixpoint push_each (b : Buf) (l : list nat) : nat :=
  match l with
  | [] => buf_len b
  | x :: r => push_each (buf_push b x) r
  end.

Fixpoint push_all (b : Buf) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: r => buf_len (buf_push b x) :: push_all b r
  end.

Fixpoint reseat_down (h : Handle) (l : list nat) : nat :=
  match l with
  | [] => handle_get h
  | x :: r => S (reseat_down (handle_reseat h x) r)
  end.

(** In a closure: the lambda's own parameter, and a captured one. *)
Definition reseat_each_value (l : list Handle) : list nat :=
  map (fun h => handle_get (handle_reseat h 1)) l.
Definition reseat_captured (h : Handle) (l : list nat) : list nat :=
  map (fun x => handle_get (handle_reseat h x)) l.

End TypedMappingAccess.

Crane Extraction "typed_mapping_access" TypedMappingAccess.
