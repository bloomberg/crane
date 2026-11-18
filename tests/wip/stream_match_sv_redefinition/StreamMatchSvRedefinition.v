From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Matching a stream literal, then a list built from its head, then the head
    itself: the nested matches each declare [auto &&_sv] in one scope
    ("redefinition of '_sv'"), and an alternative test names a type outside
    the variant ("type not found in type list"). *)
Module StreamMatchSvRedefinition.

CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).

Definition t : nat :=
  length (match sconst 0 with
          | SCons x r => match seq x (Nat.modulo x 7) with
                         | [] => @nil bool
                         | _ :: _ => match x with O => [] | S _ => [] end
                         end
          end).

End StreamMatchSvRedefinition.

Crane Extraction "stream_match_sv_redefinition" StreamMatchSvRedefinition.
