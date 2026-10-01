From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import method_body_names_later_struct.A.
From CraneTestsRegression Require Import method_body_names_later_struct.Arith.

(** This file's name begins with the inductive's, which is what makes its
    top-level functions candidates to become methods of [zed]'s struct.  The
    body names [Zed.norm], which lives in [Arith]'s struct -- emitted after
    every global-scope type, and unable to move in front of [zed]. *)
Definition le_dec (x y : zed) : bool :=
  match Zed.norm (raw_cmp x y) with Gt => false | _ => true end.
