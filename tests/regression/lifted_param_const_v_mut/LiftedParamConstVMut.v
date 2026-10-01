(** A lifted helper declares its parameters [const T] by value, and a match
    on one of them treats it as owned.

    [body] is polymorphic in a type of its own ([B]), so it is lifted to a
    top-level template, [_den_body].  Its parameters come out as
    [const Dvalue<...> u] -- a const value -- while the match on [u] is
    marked owned, so it is taken apart through [u.v_mut()]:

      error: 'this' argument to member function 'v_mut' has type
             'const Dvalue<...>', but function is not marked const

    Reduced from Vellvm's [putchar_denotation] (Semantics/Libraries.v:60),
    whose [putchar_body] is lifted to [_putchar_denotation_putchar_body];
    the same error appears twice in the install #16 residue. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Class Params := { ptr : Type ; iptr : Type ; nullp : ptr ; zeroi : iptr }.

Section DV.
  Context {Pa : Params}.

  Variant dvalue_base : Type :=
    | DVALUE_Pointer : ptr -> dvalue_base
    | DVALUE_I : nat -> nat -> dvalue_base.

  Inductive dvalue : Type :=
    | DVALUE_Base : dvalue_base -> dvalue
    | DVALUE_Struct : list dvalue -> dvalue.

  Definition show_dvalue (v : dvalue) : nat :=
    match v with DVALUE_Base _ => 0 | DVALUE_Struct _ => 1 end.

  Definition den : list dvalue -> option (sum nat dvalue) :=
    let body {B : Type} (tag : B) (u : dvalue) : option (B * dvalue) :=
      match u with
      | DVALUE_Base (DVALUE_I sz x) =>
          if Nat.eqb sz 32 then Some (tag, DVALUE_Base (DVALUE_I 8 x)) else None
      | bad => if Nat.eqb (show_dvalue bad) 0 then None else Some (tag, bad)
      end
    in
    fun args =>
      match args with
      | [c] => option_map (fun p => inr (snd p)) (body 0 c)
      | _ => None
      end.
End DV.

#[global] Instance natParams : Params :=
  {| ptr := nat ; iptr := nat ; nullp := 0 ; zeroi := 0 |}.

Module LiftedParamConstVMut.
  Definition run : option (sum nat dvalue) :=
    @den natParams [DVALUE_Base (DVALUE_I 32 5)].
End LiftedParamConstVMut.
Crane Extraction "lifted_param_const_v_mut" LiftedParamConstVMut.
