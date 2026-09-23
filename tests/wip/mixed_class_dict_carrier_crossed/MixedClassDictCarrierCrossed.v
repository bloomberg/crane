From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

(** Reduced from Vellvm's [TFunctor_modul] (rocq/Syntax/Traversal.v:859).

    Three adjacent [tfmap] calls in one instance body came out with each
    other's carriers -- [m_globals] and [m_declarations] both got the carrier
    of a sibling [Endo] dictionary, and [m_definitions] got [m_globals]'s. The
    distinguishing feature of that context is that the dictionary list is
    {e mixed-class}: a non-higher-kinded [Endo] parameter sits between the
    higher-kinded [TFunctor] ones. Every context the carrier recovery had been
    exercised on before was pure [TFunctor].

    [dict_carrier_type_args] finds the class parameter by scanning the
    callee's domains for the first one whose argument is a [Tapp] -- a carrier
    of arrow kind -- and then takes the {e argument} at that position. A
    dictionary whose class parameter is an ordinary type has the same outer
    shape and a non-[Tapp] argument, so whether it is counted decides whether
    every later position is off by one. *)

Inductive Exp (t : Set) : Set :=
| E_leaf : t -> Exp t
| E_node : Exp t -> Exp t -> Exp t.
Arguments E_leaf {t}.
Arguments E_node {t}.

Inductive Decl (t : Set) : Set := D_mk : t -> Decl t.
Arguments D_mk {t}.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

(** Not higher-kinded: its parameter is an ordinary type, so it has no carrier
    at all. This is the entry that sits between the two that do. *)
Class Endo (T : Set) := endo : T -> T.

Fixpoint exp_map {a b : Set} (f : a -> b) (e : Exp a) : Exp b :=
  match e with
  | E_leaf x => E_leaf (f x)
  | E_node l r => E_node (exp_map f l) (exp_map f r)
  end.

#[global] Instance TFunctor_exp : TFunctor Exp := fun U V f e => exp_map f e.
#[global] Instance TFunctor_decl : TFunctor Decl :=
  fun U V f d => match d with D_mk x => D_mk (f x) end.
#[global] Instance TFunctor_list {F} `{TFunctor F} : TFunctor (fun t => list (F t)) :=
  fun U V f l => map (tfmap f) l.
#[global] Instance Endo_nat : Endo nat := fun n => n.

Record modu (t : Set) : Set := mkModu
  { m_tag   : nat
  ; m_exps  : list (Exp t)
  ; m_decls : list (Decl t)
  }.
Arguments mkModu {t}.
Arguments m_tag {t}.
Arguments m_exps {t}.
Arguments m_decls {t}.

(** The mixed-class context: [Endo nat] between the two [TFunctor]s. *)
#[global] Instance TFunctor_modu
    `{TFunctor Exp} `{Endo nat} `{TFunctor Decl} : TFunctor modu :=
  fun U V f m =>
    mkModu (endo (m_tag m)) (tfmap f (m_exps m)) (tfmap f (m_decls m)).

Definition use_modu (f : nat -> bool) (m : modu nat) : modu bool := tfmap f m.

Crane Extraction "mixed_class_dict_carrier_crossed" use_modu.
