(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A mapped operation needs to declare only the headers its own text needs
    beyond those of the mapped types it takes or returns: Crane includes the
    header of every mapped type the generated code computes with, spelled or
    not.  [point] is declared by [<complex>]; [origin_at] and [on_axis]
    build and read one without a [From] of their own, and [is_real] never
    spells [point] -- the value lives in a temporary -- so only the type the
    call to [origin_at] returns asks for [<complex>]. *)

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Module CustomSignatureTypeInclude.

Axiom point : Type.
Axiom origin_at : bool -> point.
Axiom on_axis : point -> bool.

Definition is_real (b : bool) : bool := on_axis (origin_at b).

End CustomSignatureTypeInclude.

#[global] Instance point_mapping : TypeMapping CustomSignatureTypeInclude.point :=
  value_type ["complex"] (Apply "std::complex" [TypeArg (Name "double")]) UnknownCopy.
#[global] Instance origin_at_mapping : OperationMapping (Ref (@CustomSignatureTypeInclude.origin_at)) :=
  pure_cpp [] ["x0"]
    (Expr "std::complex<double>(%arg(x0) ? 1.0 : 0.0, 0.0)").
#[global] Instance on_axis_mapping : OperationMapping (Ref (@CustomSignatureTypeInclude.on_axis)) :=
  pure_cpp [] ["x0"]
    (Expr "(%arg(x0).imag() == 0.0)").
Crane Extraction "custom_signature_type_include" CustomSignatureTypeInclude.
