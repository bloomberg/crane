(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import PrimString.
From Stdlib Require Import Lists.List.
Import ListNotations.

Axiom int : Type.
Axiom zero : int.
Axiom one : int.
Axiom iplus : int -> int -> int.

Module PString.

Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | O => "O"
  | S n' => cat "S" (nat_to_string n')
  end.

Fixpoint nat_to_int (n : nat) : int :=
  match n with
  | O => zero
  | S n' => iplus one (nat_to_int n')
  end.

Fixpoint list_to_string {A : Type} (p : A -> string) (l : list A) : string :=
  match l with
  | nil => "[]"
  | cons y l' => cat (cat (p y) "::") (list_to_string p l')
  end.

End PString.

Require Crane.Extraction.

Crane Extract Inlined Constant int => "int".
Crane Extract Inlined Constant zero => "0".
Crane Extract Inlined Constant one => "1".
Crane Extract Inlined Constant iplus => "%a0 + %a1".

Require Crane.Mapping.Std.
Crane Extraction "pstring" PString.
