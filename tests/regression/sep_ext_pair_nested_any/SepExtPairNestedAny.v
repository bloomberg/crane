(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** WIP: Pattern-matching on a pair whose outer type is concrete but
    contains [std::any] in a nested position incorrectly generates
    [any_cast<pair<any,any>>].  The pair is concrete at runtime, so
    the cast throws [bad_any_cast].

    This mirrors the bug in the parse-a-lot [lex_json] wrapper:
    - [produce] returns [option (list token) * bool] where [token =
      sigT sem_ty] and [sem_ty : nat -> Type] is fixpoint-computed,
      erasing [sem_ty n] to [std::any] in the second component of [SigT].
    - Crane emits [std::pair<std::optional<List<SigT<nat,std::any>>>,bool>]
      as the concrete return type of [produce].
    - In [use_it], the pair match makes [has_tany_in_type] return true
      for the scrutinee type.  Crane wraps with [any_cast<pair<any,any>>].
      At runtime [produce] returns a concrete pair, not
      [std::pair<std::any,std::any>], so the cast throws [bad_any_cast].

    Root cause: [gen_custom_cpp_case] in translation.ml wraps with
    [any_cast<pair<any,any>>] when [is_erased_type || has_tany_in_type]
    is true.  [has_tany_in_type] fires whenever [std::any] appears
    anywhere in the type tree, even when the outer pair is concrete.
    The fix should restrict the wrapping to [is_erased_type]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(** A type family indexed by [nat].  The concrete result type depends
    on the runtime index, so [sem_ty n] erases to [std::any]. *)
Fixpoint sem_ty (n : nat) : Type :=
  match n with
  | O    => bool
  | S n' => sem_ty n'
  end.

(** A token pairs an index with a value of the corresponding type.
    The second component of the sigma erases to [std::any] because
    [sem_ty n] is not statically known. *)
Definition token : Type := { n : nat & sem_ty n }.

(** Returns a pair whose first component is [option (list token)].
    The outer pair is concrete — [option (list token) * bool] maps
    to [std::pair<std::optional<List<SigT<nat,std::any>>>,bool>].
    The [std::any] is nested inside [SigT], not at the pair level. *)
Definition produce : option (list token) * bool :=
  (None, true).

(** Extracts the second component via a pair match.  The match
    scrutinee has type [option (list token) * bool], which is a
    concrete pair with [std::any] nested inside.  [has_tany_in_type]
    fires, Crane wraps the scrutinee with [any_cast<pair<any,any>>].
    At runtime [produce] has type
    [std::pair<std::optional<List<SigT<nat,std::any>>>,bool>],
    not [std::pair<std::any,std::any>], so the cast throws
    [bad_any_cast]. *)
Definition use_it : bool :=
  match produce with
  | (_, b) => b
  end.

Crane Separate Extraction use_it produce sem_ty.
