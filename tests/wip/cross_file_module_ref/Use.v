(** Crane bug: a module instantiation is emitted as a [using] alias before the
    definition of the module it is applied to.

    [Lib3.M := F Lib.Ord] becomes [using M = F<Ord>;] at line 115, while
    [struct Ord] -- from [Lib] -- is emitted at line 121.  Crane
    forward-declares structs but not aliases, so nothing breaks the cycle.

    Three files are needed: [Lib2] exists only to declare a [bump] clashing
    with [Lib]'s, which forces both files to become structs rather than being
    flattened into the top level, and that is what interleaves them with
    [Lib3].

    Expected: [struct Ord] precedes [using M = F<Ord>].
    Actual:   error: use of undeclared identifier 'Ord'
              error: use of undeclared identifier 'M'

    Seen in Vellvm on [RM] ([Module RM := FMapAVL.Make(RawIDOrd)]), 27 times,
    plus the cascade behind it -- [FusedS] (23), [Res] (13), [global_env] (9),
    [local_env] (6), [rmap] (3) all fail immediately after their own [using]
    line because [RM] failed first. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

From CraneTestsWIP Require cross_file_module_ref.Lib.
From CraneTestsWIP Require cross_file_module_ref.Lib2.
From CraneTestsWIP Require cross_file_module_ref.Lib3.

Module CrossFileModuleRef.

  Definition use : nat := Lib3.M.twice Lib.bump + Lib2.bump 0.

End CrossFileModuleRef.

Crane Extraction "cross_file_module_ref" CrossFileModuleRef.
