(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A call of a functor parameter's member is written against the member's
    signature, and a cast of an argument to a parameter's type names the
    type the signature spells: here [D.Defs.TA.t], an alias declared in a
    module of the parameter's signature that nothing in the unit declares or
    otherwise names.  Its name was never planned, and printing the cast was
    an anomaly ("names the unmapped global ... which resolving it did not
    ask for"), as extracting ParseALot's LLPrediction was. *)

From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module FunctorParamSignatureType.

Module Type SymbolTypes.
  Parameter terminal : Type.
  Parameter eqT : forall x y : terminal, {x = y} + {x <> y}.
  Parameter semty : terminal -> Type.
End SymbolTypes.

Module DefsFn (Export Ty : SymbolTypes).
  Module TA.
    Definition t := terminal.
    Definition eq_dec : forall x y : t, {x = y} + {x <> y} := eqT.
  End TA.
  Definition t_eq_dec := TA.eq_dec.
End DefsFn.

Module Type DefsT (Ty : SymbolTypes).
  Include DefsFn Ty.
End DefsT.

Module Type T.
  Declare Module SymTy : SymbolTypes.
  Declare Module Defs : DefsT SymTy.
  Export SymTy.
  Export Defs.
End T.

Module UseFn (Import D : T).
  Definition same (t : {x : terminal & semty x}) (a : terminal) : bool :=
    match t with existT _ a' _ => if t_eq_dec a' a then true else false end.
End UseFn.

End FunctorParamSignatureType.

Crane Extraction "functor_param_signature_type" FunctorParamSignatureType.
