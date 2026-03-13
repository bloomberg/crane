(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: density and potential traces over metering-metric real-valued core. *)

From Stdlib Require Import Reals List.
Open Scope R_scope.

Module DensityPotentialTraceCase.

Definition lapse (f : R -> R) (mu : R -> R) (x : R) : R :=
  f (mu x).

Definition proper_time_static (f : R -> R) (mu : R -> R)
  (x : R) (T : R) : R :=
  lapse f mu x * T.

Definition proper_time_density_path (f : R -> R) (mu : R -> R)
  (gamma v : R -> R) (t : R) : R :=
  sqrt ((lapse f mu (gamma t))^2 - (v t)^2).

Definition V_eff (N : R -> R) (x : R) : R :=
  / (N x * N x).

Definition V_eff_massive (N : R -> R) (m : R) (x : R) : R :=
  (m ^ 2) * V_eff N x.

Definition sample_activation (z : R) : R := z.

Definition sample_mu (x : R) : R :=
  / (1 + x * x).

Definition sample_gamma (t : R) : R :=
  t / 2.

Definition sample_v (_ : R) : R :=
  / 4.

Definition sample_N (x : R) : R :=
  1 + x * x.

Definition sample_mass : R := 3.
Definition sample_time : R := 2.

Definition density_radicand_at (n : nat) : R :=
  let t := INR n in
  (lapse sample_activation sample_mu (sample_gamma t))^2 - (sample_v t)^2.

Definition static_time_nonnegative_at (n : nat) : bool :=
  if Rle_dec 0
      (proper_time_static sample_activation sample_mu (INR n) sample_time)
  then true
  else false.

Definition density_radicand_nonnegative_at (n : nat) : bool :=
  if Rle_dec 0 (density_radicand_at n)
  then true
  else false.

Definition density_value_at (n : nat) : R :=
  proper_time_density_path sample_activation sample_mu sample_gamma sample_v (INR n).

Definition density_value_nonnegative_at (n : nat) : bool :=
  if Rle_dec 0 (density_value_at n)
  then true
  else false.

Definition massive_potential_nonnegative_at (n : nat) : bool :=
  if Rle_dec 0 (V_eff_massive sample_N sample_mass (INR n))
  then true
  else false.

Definition sample_static_nonneg : bool :=
  static_time_nonnegative_at 1.

Definition sample_density_radicand_nonneg : bool :=
  density_radicand_nonnegative_at 1.

Definition sample_density_value_nonneg : bool :=
  density_value_nonnegative_at 1.

Definition sample_massive_nonneg : bool :=
  massive_potential_nonnegative_at 2.

End DensityPotentialTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "density_potential_trace" DensityPotentialTraceCase.
