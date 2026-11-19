From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.

(** A user inductive called [Comparison] and the standard library's
    [comparison] (returned by [Nat.compare]) are emitted under the same C++
    name, and the later declaration wins.  The match on [Nat.compare]'s result
    then looks for [LT] in the user's type: "no member named 'LT' in
    'UserInductiveShadowsStdlib::Comparison'".  The two types are unrelated in
    Rocq; only their emitted names collide. *)

Module UserInductiveShadowsStdlib.
  Inductive Comparison := lt_ | eq_ | gt_.

  Definition mine (c : Comparison) : nat :=
    match c with lt_ => 0 | eq_ => 1 | gt_ => 2 end.

  Definition theirs (a b : nat) : nat :=
    match Nat.compare a b with Lt => 0 | Eq => 1 | Gt => 2 end.

  (** The standard [comparison] named as a type inside the struct, where the
      bare name finds the user's [Comparison]. *)
  Definition theirs_cmp (a b : nat) : comparison :=
    if Nat.eqb a b then Eq else Lt.

  Definition run : nat :=
    mine eq_ + theirs 1 2 + match theirs_cmp 3 3 with Eq => 10 | _ => 0 end.
End UserInductiveShadowsStdlib.

Crane Extraction "user_inductive_shadows_stdlib" UserInductiveShadowsStdlib.
