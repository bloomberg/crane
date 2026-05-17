(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* NOT A BUG: src/modutil.ml line 365 — "The empty list is maybe a problem?"

   When optim_se converts Dterm(MLfix(...)) to Dfix, the recursive self-reference
   becomes MLglob(r, []) with an empty ML type arg list.

   Investigation found this is safe for Crane: gen_expr resolves template
   arguments from the C++-level environment (the function's declared template
   parameters), not from MLglob's ML type arg list. The [] is ignored.

   Verified: build_nil_list below generates `build_nil_list<T1>(n_)` in the
   recursive call — the explicit `<T1>` comes from the C++ environment, not
   from the ML type arg list. The modutil.ml comment can be removed. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TodoModutilPolyFix.

  (* Phantom type parameter A: appears only in the return type, not in value
     args. The recursive call in the extracted C++ correctly carries <T1>. *)
  Definition build_nil_list {A : Type} : nat -> list A :=
    fix go n :=
      match n with
      | O => nil
      | S n' => go n'
      end.

  Definition test_nat : list nat := build_nil_list 3.
  Definition test_bool : list bool := build_nil_list 2.

End TodoModutilPolyFix.

Crane Extraction "todo_modutil_poly_fix" TodoModutilPolyFix.
