(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test for double-call UB in the Datatypes.app extraction template.

   The template in Mapping/DequeList.v is:
     "[&]() { auto _r = %a0; _r.insert(_r.end(), %a1.begin(), %a1.end()); return _r; }()"

   The placeholder %a1 appears twice: once for .begin() and once for .end().
   When %a1 is a function call expression (not a variable), it is evaluated twice,
   producing two separate temporary deques T1 and T2.  The insert then receives
   T1.begin() and T2.end() -- iterators from different containers -- which is
   undefined behaviour.  The loop compares T1's internal iterator against T2.end()
   using raw pointer equality; since T1 and T2 are at different addresses, the
   comparison never returns true at the right position, causing the insert to
   read past T1's storage boundary.

   The fix is to introduce a temporary: auto _s = %a1; and use _s.begin(), _s.end().
*)

From Crane Require Import Mapping.NatIntStd Mapping.DequeList.
Require Crane.Extraction.

Module AppDoublecall.

(** A fixpoint function that returns a list -- when used as the second argument
    to (++) it becomes the %a1 function-call expression in the generated template,
    causing the double evaluation. *)
Fixpoint gen_list (n : nat) : list nat :=
  match n with
  | O => nil
  | S m => cons n (gen_list m)
  end.

(** When extracted, the (++) here uses the Datatypes.app template.
    gen_list a and gen_list b are both function calls, so the template
    substitutes gen_list(b) twice:
      auto _r = gen_list(a);
      _r.insert(_r.end(), gen_list(b).begin(), gen_list(b).end());  (* BUG *)
*)
Definition concat_two (a b : nat) : list nat :=
  (gen_list a) ++ (gen_list b).

End AppDoublecall.

Crane Extraction "app_doublecall" AppDoublecall.
