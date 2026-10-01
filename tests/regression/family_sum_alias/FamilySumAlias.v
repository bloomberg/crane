(** Crane bug: a named nested sum of event families (Vellvm's [CFGEtop] /
    [MCFGEtop] shape, [aE P +' bE +' cE]) is emitted as a broken alias.

    Observed:
      template <typename p = void, typename x> using AllE = Sum1<aE, Sum1, x>;
    - the inner sum [bE +' cE] has lost its arguments ([Sum1] bare), and
      [aE] its parameter [P];
    - [p = void] has a default while the following [x] does not, so the alias
      is ill-formed and every use says
        error: use of undeclared identifier 'AllE'
    Also present (same family-kind theme as itree_trigger_subevent):
      template <template <typename> class E1, template <typename> class E2,
                typename X> struct Sum1
        error: template argument for template template parameter must be a
               class template or type alias template
    [sum1]'s fields are [E1 X] / [E2 X] at the struct's own index, so it is
    declared higher-kinded, while every use passes families as plain types.

    Reduced from Vellvm's vanilla-ITree extraction,
    [Semantics/LLVMEvents.v:212]:
      Definition CFGEtop := CallE +' ExternalCallE +' IntrinsicE +' ... +' FailureE.
    emitted as [using CFGEtop = Sum1<CallE, Sum1, x>;] and then
    [use of undeclared identifier 'CFGEtop'] (17x) and, through
    [CFGtop := itree CFGEtop], [function_denotation] (34x). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module FamilySumAlias.
  Variant aE (P : Type) : Type -> Type := A : P -> aE P nat.
  Arguments A {P}.
  Variant bE : Type -> Type := B : bE unit.
  Variant cE : Type -> Type := C : cE bool.

  (* Vellvm's CFGEtop shape: a named nested sum of families, one of them
     parameterised. *)
  Definition AllE (P : Type) : Type -> Type := aE P +' bE +' cE.

  Definition t : itree (AllE nat) nat := Vis (inl1 (A 3)) (fun n => Ret n).

  Definition is_three : bool :=
    match _observe t with
    | VisF e _ => match e with inl1 (A n) => Nat.eqb n 3 | inr1 _ => false end
    | _ => false
    end.
End FamilySumAlias.

Crane Extraction "family_sum_alias" FamilySumAlias.
