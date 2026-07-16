(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   WIP test: demonstrate bad_any_cast when DequeList mapping is used.

   The bug: Crane generates any_cast<Datatypes::List<T>> in code
   that handles erased list types, but the runtime value is actually
   std::deque<T> due to the DequeList mapping. The any_cast fails
   because the stored type doesn't match.

   Pattern: A dependent record (Monoid) erases its carrier type.
   mfold takes list (m_carrier M), which becomes List<std::any> in
   any_cast. But with DequeList, the runtime value is std::deque<std::any>.
*)
From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import Nat List.
Import ListNotations.
Require Crane.Extraction.

Module DequeAnyCast.

Record Monoid := mkMonoid {
  m_carrier : Type;
  m_op : m_carrier -> m_carrier -> m_carrier;
  m_id : m_carrier
}.

Definition nat_monoid : Monoid := mkMonoid nat Nat.add 0.

Fixpoint mfold (M : Monoid) (l : list (m_carrier M)) : m_carrier M :=
  match l with
  | [] => m_id M
  | x :: rest => m_op M x (mfold M rest)
  end.

Definition test_fold_add : nat := mfold nat_monoid [1; 2; 3].

End DequeAnyCast.

Set Crane Loopify.
Crane Extraction "deque_any_cast" DequeAnyCast.
