(* WIP: When an enum constructor is used as a first-class value
   inside a functor (template context), separate extraction must
   emit it as EnumType::e_CTOR, not as a regular function call. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Inductive color := Red | Green | Blue.

Module Type ColorParam.
  Parameter default : color.
End ColorParam.

Module UseColor (P : ColorParam).
  Definition my_default : color := P.default.
  Definition color_list : list color := Red :: Green :: Blue :: nil.
  Definition is_red (c : color) : bool :=
    match c with
    | Red => true
    | _ => false
    end.
End UseColor.

Crane Separate Extraction UseColor.
