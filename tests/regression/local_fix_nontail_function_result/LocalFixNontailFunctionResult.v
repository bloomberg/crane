From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint returning a function through a non-tail recursive call
    ([let rv := go r acc in if .. then (fun _ => Leaf) else rv]), in a match
    branch, called on a literal [[]]: under CRANE_CHECK_IR=1 "closure escape:
    the local fixpoint go escapes in its generated code but nowhere in Core".
    The tail-call shapes in local_fix_returns_function and
    local_fix_function_result_inlined are fixed.  Eta-expanded to the
    function's argument, [go r acc] is a partial application, whose closure
    holds [go]: escape analysis now counts one as an escape. *)
Module LocalFixNontailFunctionResult.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition g (t : tree) : (nat -> nat) -> tree :=
  match t with
  | Leaf => let fix go (l : list tree) (acc : (nat -> nat) -> tree) {struct l} : (nat -> nat) -> tree :=
              match l with
              | [] => (fun _ => Leaf)
              | _ :: r => let rv := go r acc in (if Nat.eqb 0 1 then (fun _ => Leaf) else rv)
              end
            in go [] (fun _ => Leaf)
  | Node _ _ _ => (fun _ => Leaf)
  end.

Definition t : bool := match g Leaf (fun x => x) with Leaf => true | Node _ _ _ => false end.

End LocalFixNontailFunctionResult.

Crane Extraction "local_fix_nontail_function_result" LocalFixNontailFunctionResult.
