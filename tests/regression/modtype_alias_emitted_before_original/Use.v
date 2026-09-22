From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.Orig.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.Alias.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.User.

(** A file whose only declaration is a bare module-type alias was written ahead
    of the file it aliases:

      concept Dec = DecOrig<M>;       // use
      concept DecOrig = requires ...  // definition, two lines later

    giving [error: use of undeclared identifier 'DecOrig'].

    Files are emitted in the order {!Structure_analysis.topological_sort}
    settles, and its walk over a module's contents returned nothing at all for
    a module type.  So [Alias] named no other file, sorted with the roots, and
    was written in the first batch -- ahead of [Orig], which does name another
    file, because [tag] is a [nat].  One transposition, and only between a file
    with no dependencies and a file with one.

    Seen in Vellvm at [vellvm_bench.h:1560], [concept DecidableType =
    DecidableTypeOrig<M>], where the definition is at 1852. *)

Definition go (a b : nat) : bool := MN.same a b.

Definition tag2 : nat := tag.

Crane Extraction "modtype_alias_emitted_before_original" go tag2.
