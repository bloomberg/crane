(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: pulse-parse certificates package options, runs, and classifications into a self-checking record. *)

From Stdlib Require Import List Bool Nat.
Import ListNotations.

Module PulseParseCertificateCase.

Definition Trace := list bool.
Definition Runs := list nat.

Fixpoint first_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      if x then
        Some 0
      else
        match first_true xs' with
        | Some idx => Some (S idx)
        | None => None
        end
  end.

Fixpoint last_true (xs : Trace) : option nat :=
  match xs with
  | [] => None
  | x :: xs' =>
      match last_true xs' with
      | Some idx => Some (S idx)
      | None => if x then Some 0 else None
      end
  end.

Fixpoint trace_to_runs (xs : Trace) : Runs :=
  match xs with
  | [] => []
  | true :: xs' => 2 :: trace_to_runs xs'
  | false :: xs' => 1 :: trace_to_runs xs'
  end.

Definition pulse_base_from_runs (rs : Runs) : nat :=
  match rs with
  | [] => 1
  | x :: _ => x
  end.

Inductive PulseClass :=
| MarkShort
| MarkLong.

Definition classify_run_with_base (base n : nat) : PulseClass :=
  if Nat.leb (S base) n then MarkLong else MarkShort.

Definition classify_runs_with_base (base : nat) (rs : Runs) : list PulseClass :=
  map (classify_run_with_base base) rs.

Definition pulse_class_eqb (x y : PulseClass) : bool :=
  match x, y with
  | MarkShort, MarkShort => true
  | MarkLong, MarkLong => true
  | _, _ => false
  end.

Fixpoint pulse_class_list_eqb
    (xs ys : list PulseClass)
    : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => pulse_class_eqb x y && pulse_class_list_eqb xs' ys'
  | _, _ => false
  end.

Record PulseCertificate := {
  certificate_first_active : option nat;
  certificate_last_active : option nat;
  certificate_runs : Runs;
  certificate_base : nat;
  certificate_classes : list PulseClass
}.

Definition pulse_parse_certificate_self_consistent
    (cert : PulseCertificate)
    : bool :=
  Nat.eqb (certificate_base cert)
    (pulse_base_from_runs (certificate_runs cert))
  &&
  Nat.eqb (length (certificate_classes cert))
    (length (certificate_runs cert))
  &&
  pulse_class_list_eqb
    (certificate_classes cert)
    (classify_runs_with_base
      (certificate_base cert)
      (certificate_runs cert)).

Definition certify_trace
    (xs : Trace)
    : PulseCertificate :=
  let runs := trace_to_runs xs in
  let base := pulse_base_from_runs runs in
  let classes := classify_runs_with_base base runs in
  {| certificate_first_active := first_true xs;
     certificate_last_active := last_true xs;
     certificate_runs := runs;
     certificate_base := base;
     certificate_classes := classes |}.

Definition sample_trace : Trace :=
  [false; true; true; false; true].

Definition sample_certificate : PulseCertificate :=
  certify_trace sample_trace.

Definition sample_certificate_consistent : bool :=
  pulse_parse_certificate_self_consistent sample_certificate.

Definition sample_certificate_base : nat :=
  certificate_base sample_certificate.

Definition sample_certificate_first_active : nat :=
  match certificate_first_active sample_certificate with
  | Some idx => idx
  | None => 99
  end.

Definition sample_certificate_last_active : nat :=
  match certificate_last_active sample_certificate with
  | Some idx => idx
  | None => 99
  end.

Definition sample_certificate_class_count : nat :=
  length (certificate_classes sample_certificate).

End PulseParseCertificateCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "pulse_parse_certificate" PulseParseCertificateCase.
