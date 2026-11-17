(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An instance of a singleton class whose body forwards every one of its
    own dictionaries to a mutual fixpoint taking the same ones: the static
    method must pass them all, as Vellvm's [TFunctor_exp] does with
    [ft_exp]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module InstanceForwardsDicts.

Class Endo (T : Type) := endo : T -> T.
Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

Inductive tag := A | B.
Inductive op := C | D.
Inductive cmp := E | F.
Inductive flag := G | H.
Inductive exp (T : Set) : Set :=
| Lit : tag -> T -> exp T
| Ops : op -> cmp -> flag -> exp T
| Neg : nat -> exp T -> exp T
| EMeta : meta T -> exp T
with meta (T : Set) : Set :=
| MNull : meta T
| MExp : exp T -> meta T.
Arguments Lit {T}. Arguments Ops {T}. Arguments Neg {T}. Arguments EMeta {T}.
Arguments MNull {T}. Arguments MExp {T}.

Fixpoint ft_exp `{Endo tag} `{Endo nat} `{Endo op} `{Endo cmp} `{Endo flag} (U V : Set) (f : U -> V) (e : exp U) : exp V :=
  match e with
  | Lit t x => Lit (endo t) (f x)
  | Ops a b c => Ops (endo a) (endo b) (endo c)
  | Neg n e' => Neg (endo n) (ft_exp _ _ f e')
  | EMeta m => EMeta (ft_meta _ _ f m)
  end
with ft_meta `{Endo tag} `{Endo nat} `{Endo op} `{Endo cmp} `{Endo flag} (U V : Set) (f : U -> V) (m : meta U) : meta V :=
  match m with
  | MNull => MNull
  | MExp e => MExp (ft_exp _ _ f e)
  end.

#[global] Instance TFunctor_exp `{Endo tag} `{Endo nat} `{Endo op} `{Endo cmp} `{Endo flag} : TFunctor exp :=
  fun (U V : Set) (f : U -> V) => ft_exp U V f.

#[global] Instance Endo_tag : Endo tag := fun t => match t with A => B | B => A end.
#[global] Instance Endo_nat : Endo nat := S.
#[global] Instance Endo_op : Endo op := fun x => x.
#[global] Instance Endo_cmp : Endo cmp := fun x => x.
#[global] Instance Endo_flag : Endo flag := fun x => x.

Definition e0 : exp nat := Neg 1 (EMeta (MExp (Lit A 2))).
Definition e1 : exp nat := tfmap (fun n => n + 10) e0.

Definition sum_exp : exp nat -> nat :=
  fix go e := match e with
              | Lit A x => x
              | Lit B x => 100 + x
              | Ops _ _ _ => 0
              | Neg n e' => n + go e'
              | EMeta (MExp e') => go e'
              | EMeta MNull => 0
              end.

Definition result : nat := sum_exp e1.

End InstanceForwardsDicts.

Crane Extraction "instance_forwards_dicts" InstanceForwardsDicts.
