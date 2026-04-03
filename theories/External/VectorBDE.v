(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Mutable vector effects for the BDE flavor.

    Re-exports shared definitions from [VectorDefs.v] and adds the
    [bsl::vector] C++ type mapping. *)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export External.VectorDefs.

Crane Extract Inlined Constant vector => "bsl::vector<%t0>" From "bsl_vector.h".
