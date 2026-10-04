From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_cross_file_method.Num.

Fixpoint leb (a b : num) : bool :=
  match a, b with
  | Zero, _ => true
  | Succ _, Zero => false
  | Succ a', Succ b' => leb a' b'
  end.

Definition two : num := Succ (Succ Zero).
