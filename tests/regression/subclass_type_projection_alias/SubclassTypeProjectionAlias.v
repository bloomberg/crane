(** A type projection of a class reached through a subclass field is reduced
    at its first occurrence as at every later one.

    Reduced from Vellvm's [Run.run_program].  [state] is a field of [MS],
    a class parameterised by [Params]; the instance found for it is the
    [mm] field of [mpV].  Extraction reduces such a projection only once
    [state] is known to be a class field, which it learns by extracting the
    class -- the one the projection's own type takes as its record argument.
    That class was read off the projection's first argument, here [Params],
    so [MS] was not extracted yet at [run_program]'s signature: [state]
    stayed abstract there and spelled [crane::obj], while [Res], extracted
    after, reduced it to [State].  The match on [r] then named its
    constructors at [Sum<Err, pair<pair<obj, ...>, ...>>], another
    instantiation than [r]'s, which libc++ rejects ("a parameter pack may
    not be accessed at an out of bounds index").  The record is the last
    argument of a projection, after the class's parameters. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.
Import ITreeNotations.

Module SubclassTypeProjectionAlias.
Class Params := { ptr : Type; mkp : nat -> ptr }.
Variant err : Type := E1 | E2.

Class MS {Pa : Params} := { state : Type ; init : state }.
Class MP {Pa : Params} := { mm :: @MS Pa ; foo : nat }.

Section S.
  Context {Pa : Params}.
  Record State := { mem : list ptr }.
  Instance msV : @MS Pa := {| state := State ; init := {| mem := nil |} |}.
  Instance mpV : @MP Pa := {| mm := msV ; foo := 0 |}.
End S.

Section T.
  Context {Pa : Params}.
  Existing Instance mpV.
  Inductive dv := DV : ptr -> dv | DN : nat -> dv.
  Definition FusedS := (state * list nat)%type.
  Definition Res X := (FusedS * X)%type.

  Definition interp : itree void1 (Res dv) := Ret (init, nil, DN 3).

  Definition run_program (t : itree void1 (err + Res dv)) : itree void1 (err + dv) :=
    r <- t ;;
    Ret (match r with
         | inl e => inl e
         | inr (_, d) => inr d
         end).
End T.

#[global] Instance natParams : Params := {| ptr := nat; mkp := fun n => n |}.

Definition run (_ : unit) : itree void1 (err + dv) :=
  run_program (Pa := natParams) (ITree.map inr interp).
End SubclassTypeProjectionAlias.
Crane Extraction "subclass_type_projection_alias" SubclassTypeProjectionAlias.
