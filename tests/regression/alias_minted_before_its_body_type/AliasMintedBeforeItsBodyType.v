From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

(** A synthesised carrier alias whose body names a type defined later.

    Alias templates were collected into the file's prologue, immediately after
    the forward struct declarations. That is sound for a body naming top-level
    class templates, which can be forward-declared. [boxed] is emitted as an
    {e alias template}, and C++ has no syntax for forward-declaring one, so
    there was nothing the prologue could have declared:

      template <typename _CraneTcArg>
      using _crane_carrier_tc_... = List<boxed<_CraneTcArg>>;   // early
      ...
      template <typename t> using boxed = std::pair<Nat, Exp<t>>;

    [boxed] is deliberately not higher-kinded. A [Set -> Set] parameter is
    emitted as a plain [typename] against a use that wants
    [template <typename> class], which is a separate live defect; a test that
    fails for two unrelated reasons cannot say which one a change broke.

    Reduced by the Vellvm session from that development's four errors of this
    shape. The obstruction there is a {e nested member template} rather than an
    alias template -- [List::list], a member of the struct a module became --
    which cannot be forward-declared for a different reason. So this test
    exercises the argument the fix rests on, that an alias placed in front of
    the element that minted it is after everything that element names, and not
    the particular form of the obstruction. *)

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

Definition boxed (t : Set) : Set := (nat * Exp t)%type.

Definition bump {U V : Set} (f : U -> V) (p : boxed U) : boxed V :=
  match p with (n, e) => (n, tfmap f e) end.

#[global] Instance TFunctor_boxedlist : TFunctor (fun t => list (boxed t)) :=
  fun U V f l => List.map (bump f) l.

Definition use_boxedlist (f : nat -> bool) (l : list (boxed nat))
  : list (boxed bool) := tfmap f l.

Crane Extraction "alias_minted_before_its_body_type" use_boxedlist.
