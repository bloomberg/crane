From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From CraneTestsRegression Require Import instance_in_collision_wrapper_named_bare.Cls.

Fixpoint assoc {K V : Set} `{Dec K} (k : K) (l : list (K * V)) : option V :=
  match l with
  | nil => None
  | cons (k', v) rest => if dec k k' then Some v else assoc k rest
  end.
