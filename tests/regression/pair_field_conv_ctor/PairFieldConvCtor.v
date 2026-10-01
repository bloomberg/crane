(** A converting constructor rebuilds a [std::pair] field as one value.

    Crane gives every parametric inductive a converting constructor from
    another instantiation of itself, and it rebuilds each field of each
    constructor.  For a field whose type is another Crane inductive that works,
    because the field type has a converting constructor of its own that
    recurses [crane_any_cast] element by element.  For a field whose type is a
    [std::pair] it does not: the emitted

        this->v_ = ANN_prefix{texp<T>(a0)};

    is a functional cast between two [std::pair]s, which resolves against
    [std::pair]'s own converting constructor and so asks for
    [is_constructible_v<Dt, const std::any &>].  A Crane variant has no
    [std::any] constructor, so there is no candidate:

        error: no matching conversion for functional-style cast from
               'const texp<std::any>' to 'texp<Dt>'

    The two field kinds sit on adjacent lines of the same constructor, one
    compiling and one not, so the test carries its own control.  The recursion
    has to stop treating a pair as one value and rebuild it componentwise.

    Nothing in Rocq instantiates the constructor at [_U = std::any]: a [tfmap]
    at two concrete types gets specialised instead.  Vellvm reaches it through
    an erased higher-kinded chain; here the driver forces it directly, which
    also settles the stronger claim that the constructor body is ill-formed on
    its own terms however it is reached. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Class TFunctor (F : Set -> Set) : Type :=
  tfmap : forall (U V : Set), (U -> V) -> F U -> F V.
Arguments tfmap {F _ U V}.

Inductive dt : Set := | DI : nat -> dt | DP : dt.

Inductive exp (T : Set) : Set := | EV : T -> exp T | EN : exp T.
Arguments EV {T}. Arguments EN {T}.

#[global] Instance TFunctor_exp : TFunctor exp | 50 :=
  fun U V f e => match e with EV x => EV (f x) | EN => EN end.

Definition texp (T : Set) : Set := (T * exp T)%type.

(** The two field kinds, side by side: a Crane container that converts, and a
    [std::pair] that does not. *)
Inductive ann (T : Set) : Set :=
  | ANN_metadata : list T -> ann T
  | ANN_prefix   : texp T -> ann T.
Arguments ANN_metadata {T}. Arguments ANN_prefix {T}.

#[global] Instance TFunctor_ann : TFunctor ann | 50 :=
  fun U V f a =>
    match a with
    | ANN_metadata l  => ANN_metadata (List.map f l)
    | ANN_prefix (t, e) => ANN_prefix (f t, tfmap f e)
    end.

Definition run (a : ann nat) : ann dt := tfmap (fun n => DI n) a.

Crane Extraction "pair_field_conv_ctor" run.
