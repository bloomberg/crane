From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Minimal reproduction of the parse-a-lot LL-parser [bad_any_cast] that
    SURVIVES the [crane_erase_fn] store-site fix.

    The earlier repro (sigt_fn_any) stored a function *directly* into a field of
    type [std::any]; Crane's fix now wraps such a store in [crane_erase_fn(...)]
    so the [std::any] holds a [std::function]. That case works.

    But parse-a-lot's grammar does not store the predicate/action functions
    directly. It stores them as the two *components of a product*:

        production_semty p := predicate_semty p * action_semty p     (Defs.v:972)

    where [predicate_semty]/[action_semty] are value-dependent function types
    that Crane erases to [std::any]. So the C++ payload is
    [std::pair<std::any, std::any>], and the two lambdas are erased to
    [std::any] *through the pair conversion* — a path the [crane_erase_fn] fix
    does not cover. The lambdas are stored as raw closures, but the parser reads
    them back with [any_cast<std::function<std::any(std::any)>>] and crashes.

    This file distills exactly that product-payload shape. *)

Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

Module Make (S : SEM).

  Definition prod2 : Type := (S.idx * list S.idx)%type.

  (** predicate_semty-analog: value-dependent function type -> std::any. *)
  Definition pred_ty (p : prod2) : Type :=
    let (a, _) := p in S.sem a -> bool.

  (** action_semty-analog: value-dependent function type -> std::any. *)
  Definition act_ty (p : prod2) : Type :=
    let (a, _) := p in S.sem a -> nat.

  (** production_semty-analog: a *pair* of the two erased function types, i.e.
      C++ [std::pair<std::any, std::any>]. *)
  Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.

  (** grammar_entry-analog. *)
  Definition entry : Type := { p : prod2 & psem p }.

  (** Store the predicate/action pair. The two lambdas are erased to std::any
      through the pair conversion — the fix's crane_erase_fn is NOT applied. *)
  Definition mk (a : S.idx) (f : S.sem a -> bool) (g : S.sem a -> nat) : entry :=
    existT psem (a, []) (f, g).

  (** Look up + apply the predicate, exactly like Parser.v:113 [if p vs' ...].
      Applying just the predicate is enough to hit the crash: it is the first
      [any_cast<std::function<...>>] the parser performs. The action [g] stays in
      the stored pair so the payload keeps its product-of-erased-functions shape. *)
  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) fg =>
        let (f, _g) := fg in
        if f (arg a) then true else false
    end.

End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => nat.
End Inst.

Module M := Make Inst.

Definition my_entry : M.entry :=
  M.mk tt (fun n => Nat.eqb n 0) (fun n => S n).
Definition my_arg : forall a : Inst.idx, Inst.sem a := fun _ => 0.

(** In Rocq this is [true] (predicate [0 =? 0] holds). The extracted C++ throws
    [std::bad_any_cast] instead. *)
Definition check (u : unit) : bool := M.run my_entry my_arg.

Crane Extraction "sigt_prod_fn_any" check my_entry my_arg.
