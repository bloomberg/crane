From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** A global Core reaches unapplied, applied where it is translated.

    [fun _ no => length no] is simplified to [fun _ => length], and Core
    elaboration records [length] as named there, applied to nothing.
    Translation, generating the lambda at the two-argument type its callee
    wants, gives it its [no] back and translates the call [length no] it
    built: one Core elaboration did not reach with that many arguments, which
    CRANE_CHECK_IR reported as a call Core elaboration never saw. *)

Module EtaExtendedGlobalElaborated.

Definition both (l : list nat) (k : list nat -> list nat -> nat) : nat :=
  k (filter Nat.even l) (filter Nat.odd l).

Definition count_odds (l : list nat) : nat := both l (fun _ no => length no).

Definition count_evens (l : list nat) : nat := both l (fun yes _ => length yes).

End EtaExtendedGlobalElaborated.

Crane Extraction "eta_extended_global_elaborated" EtaExtendedGlobalElaborated.
