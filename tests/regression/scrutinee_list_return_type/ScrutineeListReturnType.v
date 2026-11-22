(** Found by Ephyra (round 22, first in the BDE flavour; the std flavour
    fails the same way). A [match] on a literal list of [inl] values, with
    list patterns of depth two, in a function returning a list of pairs.

    Expected: compiles; [result = 0] (the scrutinee has two elements).

    Fixed: compile error "no viable conversion from 'Sum<std::string,
    crane::obj>' to 'std::pair<std::string, unsigned long long>'".  The
    match was simplified to bind the scrutinee's tail
    ([auto l = List<...>::cons(Sum<...>::inl("b"), ...)]), and that list
    was spelled at the function's return type [List<std::pair<...>>]: a
    let's right-hand side fell back to the enclosing function's result
    wherever the binder's type had lost a component (here [inl]'s [nat],
    which nothing constrains, so it stays [crane::obj]).  It now falls back
    to the binder's own type, its erased parts spelled erased, and never to
    the enclosing result. *)
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
