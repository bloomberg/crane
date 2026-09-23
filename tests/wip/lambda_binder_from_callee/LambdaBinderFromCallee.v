From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

(** A lambda whose binder type the enclosing declaration never mentions.  The
    only witness is the callee's parameter type at that argument position, so
    the carrier guess is the one thing reaching the binder and it fills it with
    whichever associated type it happens to hold. *)
Class Prov := {
  provenance : Type;
  allocationId : Type;
  prov : Type;
  mk_aid : nat -> allocationId;
  aid_size : allocationId -> nat;
}.

Class Params := {
  PROV :: Prov;
  width : nat;
}.

Module LambdaBinderFromCallee.
  Section S.
    Context `{Params}.

    Definition with_aid {A : Type} (f : allocationId -> A) : A := f (mk_aid 0).

    (** [use]'s type is [nat]; [allocationId] occurs nowhere in it. *)
    Definition use : nat := with_aid (fun a => aid_size a).
  End S.
End LambdaBinderFromCallee.

Crane Extraction "lambda_binder_from_callee" LambdaBinderFromCallee.
