(** Found by Ephyra round 31.  [Datatypes.id] is declared at [crane::obj]
    (its type is the alias [ID]), so [id f x] at a function [f] applies the
    box to [x] through the erased convention and gets a box back.  Two
    defects followed.  The call recovered that box at the type its position
    expects, and then again as the declaration's own boxed result, an
    [any_cast] of a value that was no longer a box: [bad_any_cast] at run
    time.  And a match on [id f x] opened no box at all: [_sv.v()] on a
    [crane::obj] ("no member named 'v'", also seen as a Crane Bake failure).

    Fixed: a call applying more arguments than its declaration takes does not
    hand back the declaration's box ([Erasure.glob_declared_cod_erases]), and
    a scrutinee lowering typed a box is opened at the matched type
    ([Match_types.recover_erased_scrutinee]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module IdFnResultUnboxed.

CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).

Definition as_value : list nat := (id (fun _ : nat => [1])) 0.
Definition len (l : list nat) : nat := length l.
Definition as_argument : nat := len ((id (fun _ : nat => [1; 2])) 0).
Definition as_receiver : nat := length ((id (fun _ : nat => [3; 4; 5])) 0).
Definition as_number : nat := (id (fun x : nat => x + 1)) 4.
Definition dup (n : nat) : list nat := (id (fun k : nat => [k; k])) n.
Definition dup_len : nat := length (dup 3).
Definition matched_nil : nat :=
  match (id (fun _ : nat => @nil nat)) 0 with [] => 7 | _ => 1 end.
Definition head_or_7 (n : nat) : nat :=
  match (id (fun k : nat => [k])) n with [] => 7 | x :: _ => x end.
Definition matched_head : nat := head_or_7 5.
Definition stream_head : nat :=
  match (id (fun _ : bool => sconst 9)) true with SCons h _ => h end.

End IdFnResultUnboxed.

Crane Extraction "id_fn_result_unboxed" IdFnResultUnboxed.
