From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import modtype_alias_emitted_before_original.Orig.

(** A bare module-type alias, and nothing else in the file.

    Mirrors [Stdlib/Structures/DecidableType.v:26]

      Module Type DecidableType := Equalities.DecidableTypeOrig.

    Emitted as [concept Dec = DecOrig<M>;], so it cannot precede [DecOrig]. *)

Module Type Dec := DecOrig.
