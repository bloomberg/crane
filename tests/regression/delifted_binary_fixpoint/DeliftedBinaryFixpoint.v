From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import BinPos.

(** A local fixpoint of two arguments that is not lifted to a helper, because
    its return type is recovered from its body.  Every other de-lifted
    fixpoint in the suite is unary, and a unary one cannot show whether the
    self-call passes all of its arguments: [_self_go(_self_go, p)(x)] and
    [_self_go(_self_go, p, x)] differ only from arity two up.

    This does not reproduce the curried spine -- the optimiser uncurries this
    body before translation sees it, whichever way the recursion is written.
    It covers the arity-two de-lift path, which nothing else did. *)

Module DeliftedBinaryFixpoint.
  Definition same (a b : positive) : bool :=
    (fix go (p : positive) : positive -> bool :=
       match p with
       | xH => fun x => match x with xH => true | _ => false end
       | xO p' => fun x => match x with xO x' => go p' x' | _ => false end
       | xI p' => fun x => match x with xI x' => go p' x' | _ => false end
       end) (xO a) (xO b).
End DeliftedBinaryFixpoint.

Crane Extraction "delifted_binary_fixpoint" DeliftedBinaryFixpoint.
