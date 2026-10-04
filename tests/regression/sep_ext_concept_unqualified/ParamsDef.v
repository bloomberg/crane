From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Class Provenance := { prov : Set }.
Class Params := { PROV :: Provenance }.
