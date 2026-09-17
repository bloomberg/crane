(** Crane bug: an instance declared in a file that is emitted as a struct is
    lifted to namespace scope, but its use sites still qualify it with that
    file's name.

      193 | struct StringUtil { ... };        // no showN in it
      203 | struct showN { ... };             // lifted, correctly
          | StringUtil::showN::show(n)        // still qualified

    Expected: [showN::show(n)].
    Actual:   error: no member named 'showN' in 'StringUtil'; did you mean
                     simply 'showN'?

    The lift itself is the 697c44518 fix for an instance declared outside the
    extraction root; what is left is that the references were not updated with
    it.

    [banner] exists in both files so that neither is flattened into the top
    level -- a struct for the file is what the stale qualification names.

    Seen in Vellvm on [Utils/StringUtil.v]: 6 "no member named 'X' in
    'StringUtil'" ([showN], [showZ]) plus 2 "no template named 'showOpt' in
    'StringUtil'". *)

From Crane Require Extraction.
From Stdlib Require Import String.

Class Show (T : Type) : Type := { show : T -> string ; name : string }.

#[global] Instance showN : Show nat :=
  {| show := fun _ : nat => "n"%string ; name := "nat"%string |}.
#[global] Instance showB : Show bool :=
  {| show := fun b : bool => if b then "t"%string else "f"%string ; name := "bool"%string |}.

(* Enough else in the file that it is emitted as a struct. *)
Definition parens (s : string) : string := ("(" ++ s ++ ")")%string.
Definition banner : string := "u"%string.
