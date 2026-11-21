From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_callee_alias_type_head.Lib.

Module Lab <: L. Definition Label := nat. End Lab.
Module LX := LexFn Lab.
Module SL := SemFn Lab LX.
