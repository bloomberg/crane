(** Crane bug: at [E := void1] (a logical family, erased since 0db93f5fe),
    a constructor inside an anonymous function passed to a polymorphic
    function has its *result* type's components erased too.

    Observed ([step] below):
      return apply_step<std::any, std::pair<Nat, Nat>, Nat>(
          [](std::pair<Nat, Nat> pat) { ...
              return tree<std::any, Sum<std::pair<std::any, std::any>, std::any>>::
                  go(treeF<std::any, Sum<std::pair<Nat, Nat>, Nat>, ...>::retf(...));
    The outer [tree<...>] should be [tree<std::any, Sum<std::pair<Nat, Nat>, Nat>>];
    only the family is logical, [(nat * nat) + nat] is not.  Diagnostics:
      error: no matching conversion for functional-style cast from
             'const std::function<tree<std::any, Sum<std::pair<Nat, Nat>, Nat>> (std::any)>'
             to 'std::function<tree<std::any, Sum<std::pair<std::any, std::any>, std::any>> (std::any)>'
      error: no viable conversion from returned value of type
             'tree<[...], Sum<pair<std::any, std::any>, std::any>>' to function
             return type 'tree<[...], Sum<pair<Nat, Nat>, Nat>>'

    Control: the identical file at a local empty family
    ([Variant noE : Type -> Type := .]) instead of [void1] compiles.

    Reduced from the extracted ITree library: an [ITree.iter] countdown over
    [void1] (Vellvm's top level is [itree void1 bool]) gives exactly this for
    the step lambda [fun '(k, acc) => ... Ret (inr acc) ...]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module Void1LambdaResultErased.
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

  Variant noE : Type -> Type := .

  Fixpoint run (fuel : nat) (t : tree noE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e _ => match e with end
             end
    end.

  Definition apply_step {E : Type -> Type} {A B : Type}
    (f : A -> tree E (A + B)) (a : A) : tree E (A + B) := f a.

  (* ITree.iter's step, an anonymous pattern-matching lambda passed to a
     polymorphic function. *)
  Definition step (p : nat * nat) : tree void1 ((nat * nat) + nat) :=
    apply_step (fun '(k, acc) =>
      match k with
      | O => go (RetF (inr acc))
      | S k' => go (RetF (inl (k', S acc)))
      end) p.

  Definition first (p : nat * nat) : nat :=
    match observe (step p) with
    | RetF (inr a) => a
    | RetF (inl (k, _)) => k
    | _ => 0
    end.

  Definition is_three : bool := Nat.eqb (first (4, 0)) 3.
End Void1LambdaResultErased.

Crane Extraction "void1_lambda_result_erased" Void1LambdaResultErased.
