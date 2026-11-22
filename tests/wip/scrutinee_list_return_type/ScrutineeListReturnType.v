(** Found by Ephyra (round 22, first in the BDE flavour; the std flavour
    fails the same way). A [match] on a literal list of [inl] values, with
    list patterns of depth two, in a function returning a list of pairs.

    Expected: compiles; [result = 0] (the scrutinee has two elements).

    Actual: compile error "no viable conversion from 'Sum<std::string,
    crane::obj>' to 'std::pair<std::string, unsigned long long>'". The
    match is simplified to bind the scrutinee's tail
    ([auto l = List<...>::cons(Sum<...>::inl("b"), ...)]), but that list is
    spelled at the function's return type [List<std::pair<...>>] instead of
    [List<Sum<std::string, nat>>]; the [Sum]'s second parameter is also
    erased to [crane::obj] (and under BDE its string is [std::string], not
    [bsl::string]). Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.
Module ScrutineeListReturnType.
Definition pairs (u : bool) : list (PrimString.string * nat) :=
  match [@inl PrimString.string nat "a"%pstring; @inl PrimString.string nat "b"%pstring] with
  | [] => []
  | [_] => [("x"%pstring, 1)]
  | _ :: _ :: _ => []
  end.
Definition result : nat := List.length (pairs true).
End ScrutineeListReturnType.
Crane Extraction "scrutinee_list_return_type" ScrutineeListReturnType.
