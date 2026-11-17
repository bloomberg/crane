(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A mapped operation needs to declare only the headers its own text needs
    beyond those of the mapped types it takes or returns: Crane includes the
    header of every mapped type the generated code computes with, spelled or
    not.  [point] is declared by [<complex>]; [origin_at] and [on_axis]
    build and read one without a [From] of their own, and [is_real] never
    spells [point] -- the value lives in a temporary -- so only the type the
    call to [origin_at] returns asks for [<complex>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module CustomSignatureTypeInclude.

Axiom point : Type.
Axiom origin_at : bool -> point.
Axiom on_axis : point -> bool.

Definition is_real (b : bool) : bool := on_axis (origin_at b).

End CustomSignatureTypeInclude.

Crane Extract Inlined Constant CustomSignatureTypeInclude.point => "std::complex<double>" From "complex".
Crane Extract Inlined Constant CustomSignatureTypeInclude.origin_at => "std::complex<double>(%a0 ? 1.0 : 0.0, 0.0)".
Crane Extract Inlined Constant CustomSignatureTypeInclude.on_axis => "(%a0.imag() == 0.0)".
Crane Extraction "custom_signature_type_include" CustomSignatureTypeInclude.
