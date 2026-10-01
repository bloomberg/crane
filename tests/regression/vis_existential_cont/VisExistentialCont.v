(** Crane bug: a [VisF] built from a literal continuation types the
    continuation's *result* as [std::any] instead of the tree.

    Observed ([t] below):
      treeF<askE, Nat, tree<askE, Nat>>::visf(askE::ask(...),
          std::function<std::any(std::any)>([](const std::any &n) -> std::any {
            return tree<askE, Nat>::go(... retf(Nat::s(std::any_cast<Nat>(n)))); }))
    The argument side is right (the existential [X] is erased and the body
    casts [n] back to [Nat]).  The field is [std::function<T(std::any)>]
    with [T = tree<askE, Nat>], so the continuation must return that.
    Diagnostic:
      error: no viable conversion from 'function<std::any (std::any)>' to
             'function<tree<askE, Nat> (std::any)>'

    Possibly the same layer as family_sum_alias's remaining failure, and a
    sibling of vis_cont_type (that one is a continuation built by wrapping
    an existing one inside a generic function; this one is a lambda literal
    at a concrete type).

    Reduced from Vellvm's vanilla-ITree extraction: every
    [Vis e (fun x => ...)] / [trigger] result continuation; also ITree's own
    [ITree.trigger e := Vis e (fun x => Ret x)]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module VisExistentialCont.
  Variant treeF (E : Type -> Type) (R : Type) (T : Type) : Type :=
  | RetF (r : R)
  | TauF (t : T)
  | VisF {X : Type} (e : E X) (k : X -> T).
  Arguments RetF {E R T}.
  Arguments TauF {E R T}.
  Arguments VisF {E R T X}.

  CoInductive tree (E : Type -> Type) (R : Type) : Type :=
    go { observe : treeF E R (tree E R) }.
  Arguments go {E R}.
  Arguments observe {E R}.

  Variant askE : Type -> Type := Ask : nat -> askE nat.

  (* A Vis whose existential X is nat at construction ([Ask 2 : askE nat]),
     with a continuation that uses its argument at that type. *)
  Definition t : tree askE nat := go (VisF (Ask 2) (fun n => go (RetF (S n)))).

  Definition answer (fuel : nat) (t : tree askE nat) : option nat :=
    match observe t with
    | VisF e k => match e in askE X return (X -> tree askE nat) -> option nat with
                  | Ask n => fun k => match observe (k n) with RetF r => Some r | _ => None end
                  end k
    | RetF r => Some r
    | TauF _ => None
    end.

  Definition is_three : bool :=
    match answer 1 t with Some n => Nat.eqb n 3 | None => false end.
End VisExistentialCont.

Crane Extraction "vis_existential_cont" VisExistentialCont.
