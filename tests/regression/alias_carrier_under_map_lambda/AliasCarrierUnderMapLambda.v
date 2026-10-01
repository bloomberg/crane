From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

(** A [tfmap] whose carrier is an {e alias} -- [texp t := (t * Exp t)] -- is
    given a synthesised carrier alias and spelled when it appears as an
    ordinary subterm, but {e not} when it appears inside an inline lambda
    passed to [List.map]. There the emitter writes no carrier at all and hands
    the site to deduction:

      Tv::tfmap([](auto&& _ec0, texp<std::any> _ec1) { ... }, f, te)

    Deduction sees through [texp] to [std::pair] and deduces [T1 = std::pair],
    so the call does not match:

      error: no matching function for call to 'tfmap'

    Hoisting the mapped function to a named top-level definition -- changing
    nothing else, keeping [List.map], the pair, the alias carrier and the
    destructuring binder -- makes the same body mint a carrier and compile.
    That control is what rules out those four as the cause: the inline lambda
    is necessary, not merely sufficient. So the defect is not "an alias carrier
    cannot be deduced" (though it cannot); it is that the inline-lambda path
    skips the mint the named path performs.

    [TFunctor] must stay a single-method class: a braces-and-fields class is
    emitted as a concept with a member carrier alias, which spells every
    carrier and reproduces nothing. Nothing is inside a [Module], because the
    synthesised alias is emitted at namespace scope while its body would name a
    type inside the module -- a second, unrelated defect. *)

Inductive Exp (t : Set) : Set :=
| E_leaf : t -> Exp t
| E_node : Exp t -> Exp t -> Exp t.
Arguments E_leaf {t}.
Arguments E_node {t}.

(** An alias carrier: arity 1, body arity 2. *)
Definition texp (t : Set) : Set := (t * Exp t)%type.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

Fixpoint exp_map {a b : Set} (f : a -> b) (e : Exp a) : Exp b :=
  match e with
  | E_leaf x => E_leaf (f x)
  | E_node l r => E_node (exp_map f l) (exp_map f r)
  end.

#[global] Instance TFunctor_exp : TFunctor Exp :=
  fun U V f e => exp_map f e.

#[global] Instance TFunctor_texp : TFunctor texp :=
  fun U V f p => (f (fst p), exp_map f (snd p)).

#[global] Instance TFunctor_list {F} `{TFunctor F} : TFunctor (fun t => list (F t)) :=
  fun U V f l => map (tfmap f) l.

Inductive instr (t : Set) : Set :=
| I_op   : Exp t -> instr t
| I_call : texp t -> list (texp t * nat) -> instr t.
Arguments I_op {t}.
Arguments I_call {t}.

#[global] Instance TFunctor_instr : TFunctor instr :=
  fun U V f i =>
    match i with
    | I_op o => I_op (tfmap f o)
    | I_call fn args =>
        (* The sibling [tfmap f fn] is spelled and compiles; the one inside the
           [List.map] lambda is the defect. *)
        I_call (tfmap f fn) (List.map (fun '(te, a) => (tfmap f te, a)) args)
    end.

Definition use_instr (f : nat -> bool) (i : instr nat) : instr bool := tfmap f i.

Crane Extraction "alias_carrier_under_map_lambda" use_instr.
