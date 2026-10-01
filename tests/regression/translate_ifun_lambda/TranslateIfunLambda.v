(** Crane bug: [translate inr1] (an event-family morphism [E ~> F] given as
    an eta-expanded constructor) does not compile.

    Observed:
      return Interp::template translate<bE, std::any, T1>(
          [](axiom, bE x0) {
            return Sum1<std::any, std::any, std::any>::inr1(x0);
          },
          x);
    - the erased type abstraction of [IFun] ([forall T, E T -> F T]) is kept
      as a lambda parameter of type [axiom]:
        error: unknown type name 'axiom'
    - the target family is written [std::any], both as [translate]'s second
      type argument and in [Sum1<std::any, std::any, std::any>::inr1], where
      it should be [Sum1<AE, bE, std::any>]:
        error: no viable conversion from returned value of type
               'Itree<std::any, [...]>' to function return type
               'Itree<Sum1<AE, bE, std::any>, [...]>'
    - and then [no matching function for call to object of type '(lambda)']
      inside [translateF], and [no matching function for call to 'translate']
      at its recursive call (possibly the cofix_self_call_targs layer).

    Reduced from Vellvm's vanilla-ITree extraction:
    [Semantics/LLVMEvents.v:216], [Definition withCall : MCFGtop ~> CFGtop :=
    translate inr1.] emitted as [[](axiom, std::any x0) { ... }]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module TranslateIfunLambda.
  Variant aE : Type -> Type := A : aE nat.
  Variant bE : Type -> Type := B : nat -> bE nat.

  (* Vellvm's [withCall : MCFGtop ~> CFGtop := translate inr1]. *)
  Definition lift : itree bE ~> itree (aE +' bE) := translate inr1.

  Definition t : itree (aE +' bE) nat := lift _ (Ret 3).

  Definition is_three : bool :=
    match _observe t with
    | RetF n => Nat.eqb n 3
    | _ => false
    end.
End TranslateIfunLambda.

Crane Extraction "translate_ifun_lambda" TranslateIfunLambda.
