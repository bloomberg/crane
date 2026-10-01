(** Crane bug: a [let]-bound helper whose body raises through a
    subevent-polymorphic function ([raiseUB {E} `{ubE -< E}]) is lifted
    with its event family generalised to a fresh template parameter, and
    the call site fills that parameter with the enclosing definition's
    type.

    Observed (72fb02926), inside a [Context {Pa : Params}] section:
      template <typename _tcI0, typename T1>
      static Itree<T1, Nat> _puts_body(const Nat u) {       // family generalised to T1
        ...
        return ITree::template iter<std::any, Nat, std::pair<Nat, Nat>>(
            ... Monad0::template ret<Monad_itree, ...>(...) ...);   // family erased, instance bare
      ...
      _puts_body<_tcI0, function_denotation<typename _tcI0::ptr>>(a0)   // T1 := the enclosing type
    The let's annotation fixes the family ([top nat := itree AllE nat]), so
    there is nothing to generalise; the helper should return
    [Itree<AllE<...>, Nat>] and the call pass only [_tcI0].  Diagnostic:
      error: no matching function for call to 'ret'
    (With a plain [Context {P : Type}] instead of the class, the call is
    still [_puts_body<top<...>>] but the body happens to compile.)

    Reduced from Vellvm, [Semantics/Libraries.v] [puts_denotation]
    ([let puts_body (u_strptr : dvalue) : CFGtop dvalue := match ... |
    bad => raiseUB ... end in fun args => ... inr <$> puts_body char ...]):
    Vellvm's last three [ret] errors on 72fb02926
    ([_puts_denotation_puts_body<_tcI0, function_denotation<...>>]). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad Structures.Functor.
Import ListNotations.
Import ITreeNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Module LiftedHelperFamilyGeneralised.
  Variant ubE : Type -> Type := ThrowUB : nat -> ubE void.
  (* Vellvm's LLVMEvents.raiseUB: polymorphic in the family through a
     subevent constraint. *)
  Definition raiseUB {E : Type -> Type} `{ubE -< E} {X} (n : nat) : itree E X :=
    v <- trigger (ThrowUB n) ;; match v : void with end.

  Class Params : Type := { ptr : Type ; zero : ptr }.
  Section WithParam.
    Context {Pa : Params}.
    Variant aE : Type -> Type := A : ptr -> aE nat.
    Definition AllE := aE +' ubE.
    Definition top := itree AllE.
    Definition function_denotation : Type := list nat -> top (nat + nat).

    (* Vellvm's Libraries.puts_denotation shape, with the raiseUB branch. *)
    Definition puts : function_denotation :=
      let body (u : nat) : top nat :=
        match u with
        | O => raiseUB 0
        | S k => ITree.iter (fun '(c, off) =>
                   if Nat.eqb c 0 then ret (inr off) else ret (inl (pred c, S off))) (k, 0)
        end
      in
      fun args => match args with
                  | [x] => inr <$> body x
                  | _ => ret (inl 0)
                  end.
  End WithParam.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition c : top (nat + nat) := puts [3].
End LiftedHelperFamilyGeneralised.

Crane Extraction "lifted_helper_family_generalised" LiftedHelperFamilyGeneralised.
