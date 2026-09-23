From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

(** A higher-kinded class whose carrier is a {e composition} -- [fun t =>
    option (Exp t)] -- is recovered correctly at a top-level call, where the
    emitter writes the synthesised alias:

      Tv::template tfmap<_crane_carrier_tc>(...)   // option (Exp t)

    but the same carrier reached through a {e record field}, in the traversal
    Crane generates for the record, is written as the bare head:

      Tv::template tfmap<std::optional>(...)       // WRONG

    [TFunctor<std::optional>] wants [std::optional<std::any>], while the
    adapter lambda emitted beside it takes [std::optional<Exp<std::any>>]:

      error: no matching function for call to 'tfmap'
      note: no known conversion from '(lambda ...)' to
        'std::type_identity_t<TFunctor<std::optional>>' (aka
        'std::function<std::optional<std::any>(..., std::optional<std::any>)>')

    The [g_anns : list (Exp t)] field is the control: it takes the same wrong
    path and is emitted as the bare [tfmap<List>], but it compiles, because
    [List] is Crane's own type and its element-wise converting constructor
    absorbs the mismatch. Ownership of the carrier decides whether the defect
    is visible, not whether it is present -- so a repair that special-cases
    std-mapped carriers would silence the error and leave the wrong carrier at
    every Crane-owned field.

    [TFunctor] must stay a single-method class: a braces-and-fields class is
    emitted as a concept with a member carrier alias, which spells every
    carrier and reproduces nothing. Nothing here is inside a [Module], because
    the synthesised alias is emitted at namespace scope while its body names
    [Exp] from inside the module -- a second, unrelated defect that would be
    reported by the same test. *)

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

#[global] Instance TFunctor_exp : TFunctor Exp :=
  fun U V f e => exp_map f e.

#[global] Instance TFunctor_option {F} `{TFunctor F} : TFunctor (fun t => option (F t)) :=
  fun U V f o => match o with Some x => Some (tfmap f x) | None => None end.

#[global] Instance TFunctor_list {F} `{TFunctor F} : TFunctor (fun t => list (F t)) :=
  fun U V f l => map (tfmap f) l.

Record glob (t : Set) : Set := mkGlob
  { g_name : t
  ; g_exp  : option (Exp t)
  ; g_anns : list (Exp t)
  }.
Arguments mkGlob {t}.
Arguments g_name {t}.
Arguments g_exp {t}.
Arguments g_anns {t}.

#[global] Instance TFunctor_glob : TFunctor glob :=
  fun U V f g =>
    mkGlob (f (g_name g))
           (tfmap f (g_exp g))
           (tfmap f (g_anns g)).

(** The composed carrier at a top-level argument: this one is already correct,
    and is kept as the control that says the emitter can do it. *)
Definition use_option (f : nat -> nat) (o : option (Exp nat)) : option (Exp nat) :=
  tfmap f o.

(** The same carrier through a record field. *)
Definition use_glob (f : nat -> nat) (g : glob nat) : glob nat := tfmap f g.

Crane Extraction "tfunctor_record_field_carrier" use_option use_glob.
