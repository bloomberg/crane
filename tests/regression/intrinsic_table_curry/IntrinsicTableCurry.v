(** Crane bug: in a list literal of pairs whose second component is a
    two-argument function alias ([semantic_function := list nat -> option
    ptr -> itree E (nat + nat)]), the inner cons cells spell the element
    type *curried* while the outer cells and the alias are uncurried.

    Observed (f049d191d):
      List<std::pair<Nat, std::function<Itree<T1, Sum<Nat, Nat>>(List<Nat>, std::optional<ptr>)>>>::cons(  // outer: uncurried
          ...,
          List<std::pair<Nat, std::function<std::function<Itree<T1, Sum<Nat, Nat>>(std::optional<ptr>)>(List<Nat>)>>>::cons(  // inner: curried
    Diagnostics:
      error: no viable conversion from 'pair<[...], function<Itree<FailE, Sum<Nat, Nat>> (List<Nat>, std::optional<Nat>)>>'
             to 'pair<[...], std::function<std::function<Itree<FailE, Sum<Nat, Nat>> (std::optional<Nat>)> (List<Nat>)>>'
      error: no matching constructor for initialization of
             'std::function<std::function<Itree<...>> (std::optional<Nat>)> (List<Nat>)>'
    Needs the ingredients below (a Params section, a subevent-constrained
    family, elements from a function returning the alias mixed with a
    constant of the alias); a plain two-argument alias in a five-element
    list does not reproduce it.

    Reduced from Vellvm, [Semantics/IntrinsicsDefinitions.v:380, 629]
    ([semantic_function], [defined_intrinsics := [ (fabs_32_decl,
    pure_base_to_semantic llvm_fabs_f32) ; ... ; (va_start_decl,
    llvm_va_start) ; ... ]]): found behind Vellvm's last errors on
    f049d191d after hand-fixing them.

    (Aside, not this test: a definition named [va_start] collides with the
    <cstdarg> macro -- "too many arguments provided to function-like macro
    invocation" -- so the constant here is called [my_vastart].) *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From ITree Require Import ITree.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

Module IntrinsicTableCurry.
  Class Params : Type := { ptr : Type ; zero : ptr }.
  Variant failE : Type -> Type := Fail : failE void.

  Section Intrinsics.
    Context {Pa : Params}.
    Context {E : Type -> Type} `{failE -< E}.

    (* Vellvm's IntrinsicsDefinitions.v:378-383 *)
    Definition pure_function : Type := list nat -> option (nat + nat).
    Definition semantic_function : Type := list nat -> option ptr -> itree E (nat + nat).
    Definition intrinsic_definitions : Type := list (nat * semantic_function).

    Definition to_itree (o : option (nat + nat)) : itree E (nat + nat) :=
      match o with Some r => Ret r | None => v <- trigger Fail ;; match v : void with end end.

    Definition pure_to_semantic : pure_function -> semantic_function :=
      fun f args _ => to_itree (f args).

    Definition p1 : pure_function := fun args => match args with [a] => Some (inl (S a)) | _ => None end.
    Definition p2 : pure_function := fun args => match args with [a] => Some (inl (a + a)) | _ => None end.

    Definition my_vastart : semantic_function :=
      fun args varargs => match args, varargs with
                          | [a], Some _ => Ret (inl a)
                          | _, _ => to_itree None
                          end.

    (* IntrinsicsDefinitions.v:629 *)
    Definition defined : intrinsic_definitions :=
      [ (1, pure_to_semantic p1) ; (2, pure_to_semantic p2) ; (3, pure_to_semantic p1) ;
        (4, pure_to_semantic p2) ; (5, my_vastart) ; (6, pure_to_semantic p1) ].
  End Intrinsics.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition count : nat := length (defined (E := failE)).
  Definition is_six : bool := Nat.eqb count 6.
End IntrinsicTableCurry.

Crane Extraction "intrinsic_table_curry" IntrinsicTableCurry.
