(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a lambda written as an element of a list literal, building a
    value of a mapped inductive, gets that value's type arguments erased.
    [[fun x => Some x] : list (nat -> option nat)] emits the body
    [std::make_optional<crane::obj>(crane::obj(x))], and the lambda then
    does not convert to the element type
    [crane::fn<std::optional<uint64_t>(uint64_t)>]; [fun x => (x, x)] does
    the same with [std::make_pair].  The element's function type never
    reaches the lambda's body.  The same lambda on its own, as a function
    argument, or inside a pair or an option works, as does a user-defined
    option type in the list. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ListLiteralLambdaMappedResult.

Definition fs : list (nat -> option nat) := [fun x => Some x].

Definition from_option : nat := match List.hd (fun _ => None) fs 4 with Some x => x | None => 0 end.

Definition gs : list (nat -> nat * nat) := [fun x => (x, x)].

Definition from_pair : nat := fst (List.hd (fun x => (x, x)) gs 3).

End ListLiteralLambdaMappedResult.

Crane Extraction "list_literal_lambda_mapped_result" ListLiteralLambdaMappedResult.
