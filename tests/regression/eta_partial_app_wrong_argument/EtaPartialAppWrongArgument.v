From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A function-typed recursive call [z r []] used as a local fixpoint's
    accumulator is eta-expanded to [[=](uint64_t) -> bool { return z(a1_value,
    _pa1, _loop_x0); }]: the lambda's parameter is left unnamed and the call
    passes the loop's accumulator ([crane::fn<bool(uint64_t)>]) in its place,
    "no viable conversion from 'const crane::fn<bool (uint64_t)>' to
    'uint64_t'".  The eta-expansion's parameter is [_x0], spelled like
    [go]'s accumulator, and the tail loop renamed every [_x0] to [_loop_x0],
    the lambda's own included.  The renaming now stops at a lambda whose
    parameter shadows the name. *)
Module EtaPartialAppWrongArgument.

Fixpoint z (l : list nat) (m : list nat) {struct l} : nat -> bool :=
  match l, m with
  | [], _ => (fun _ => true)
  | _ :: _, [] => (fun _ => true)
  | _ :: r, y :: s =>
    let fix go (k : list bool) (acc : nat -> bool) {struct k} : nat -> bool :=
      match k with
      | [] => (let cf := (fun _ : nat => false) in let cg := (fun _ : nat => y) in fun c : nat => cf (cg c))
      | _ :: rest => go rest (z r [])
      end in go [] (z r s)
  end.

Definition t : bool := z [1] [2] 0.

End EtaPartialAppWrongArgument.

Crane Extraction "eta_partial_app_wrong_argument" EtaPartialAppWrongArgument.
