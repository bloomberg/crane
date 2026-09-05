From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module TypeConstructorParamInductive.

(** An inductive parameterised by a type {e constructor} emits a template
    template parameter that its instantiations do not satisfy. *)
Inductive wrapped (F : Type -> Type) (A : Type) : Type :=
| Wrap : F A -> wrapped F A
| Pair2 : F A -> F A -> wrapped F A.
Arguments Wrap {F A}.
Arguments Pair2 {F A}.

Definition size_list (w : wrapped list nat) : nat :=
  match w with
  | Wrap l => length l
  | Pair2 a b => length a + length b
  end.

Definition size_opt (w : wrapped option nat) : nat :=
  match w with
  | Wrap o => match o with Some _ => 1 | None => 0 end
  | Pair2 a b => (match a with Some _ => 1 | None => 0 end)
               + (match b with Some _ => 1 | None => 0 end)
  end.

Definition total : nat :=
  size_list (Wrap [1;2;3]) + size_list (Pair2 [1] [2;3])
  + size_opt (Wrap (Some 1)) + size_opt (Pair2 (Some 1) None).

End TypeConstructorParamInductive.
Crane Extraction "type_constructor_param_inductive" TypeConstructorParamInductive.
