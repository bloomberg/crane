From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_promoted_alias_import.ProvDef.

Class Pointer {P : Provenance} := { ptr : Type; mk_ptr : prov -> ptr }.
Class Params := { PROV :: Provenance; PTR :: @Pointer PROV }.
