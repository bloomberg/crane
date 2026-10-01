From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

(** A higher-kinded carrier whose traversed type sits inside a {e pair}.

    [dict_carrier_type_args] recovers the carrier by abstracting the
    dictionary's codomain over the type the traversal varies in, and found
    that type by descending the {e leading} argument of each application.
    That conflates two questions -- how far to descend, and which argument the
    composition is applied in -- which coincide only while every constructor
    in the chain takes one argument. A pair separates them: the descent takes
    the first component and abstracts over [option nat], giving a carrier of
    the right shape varying in the wrong place.

    Deliberately none of the three contexts that produced the neighbouring
    carrier defects: no mixed-class dictionary list, no [List.map] lambda over
    an erased binder, no dictionary reached through a class constraint. What
    is left is the pair.

    The first component is an [option] rather than a bare [nat] so the defect
    is observable. A wrong carrier is usually latent: every Crane-owned type
    has an element-wise converting constructor that absorbs the difference
    through [std::any]. [std::optional] has none, so the mismatch is an
    error rather than a silently wrong instantiation. *)

Inductive Exp (t : Set) : Set :=
| E_leaf : t -> Exp t
| E_node : Exp t -> Exp t -> Exp t.
Arguments E_leaf {t}.
Arguments E_node {t}.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

Fixpoint exp_map {a b : Set} (f : a -> b) (e : Exp a) : Exp b :=
  match e with
  | E_leaf x => E_leaf (f x)
  | E_node l r => E_node (exp_map f l) (exp_map f r)
  end.

#[global] Instance TFunctor_exp : TFunctor Exp := fun U V f e => exp_map f e.

(** The traversed type under a pair. *)
#[global] Instance TFunctor_tagged : TFunctor (fun t => list (option nat * Exp t)) :=
  fun U V f l => map (fun p => (fst p, exp_map f (snd p))) l.

Record blk (t : Set) : Set := mkBlk
  { b_id   : nat
  ; b_code : list (option nat * Exp t)
  }.
Arguments mkBlk {t}.
Arguments b_id {t}.
Arguments b_code {t}.

#[global] Instance TFunctor_blk : TFunctor blk :=
  fun U V f b => mkBlk (b_id b) (tfmap f (b_code b)).

Definition use_blk (f : nat -> bool) (b : blk nat) : blk bool := tfmap f b.

Crane Extraction "carrier_traversed_under_pair" use_blk.
