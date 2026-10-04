From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_cross_file_method.Num.
From CraneTestsRegression Require Import sep_ext_cross_file_method.NumOps.

(** A function on [num] in a file whose name begins with the type's, as
    [ZArith_dec] does with [Z]: by name it is a "wrapper" of [num], but under
    separate extraction it must stay in its own file -- as a method of [num]
    it would land in Num.h, naming [NumOps.two], and NumOps.h includes
    Num.h. *)
Definition num_le_two (a : num) : bool := leb a two.
