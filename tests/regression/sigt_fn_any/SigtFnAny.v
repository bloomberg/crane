From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Regression test for the [bad_any_cast] Crane bug hit by parse-a-lot's
    LL parser (now fixed).

    The parser stores, per grammar production, a semantic predicate/action
    *function* inside a dependent pair

        grammar_entry := { p : production & production_semty p }

    where [production_semty p] is a *value-dependent* function type
    (theories/Parser/Defs.v). Because that payload type depends on the runtime
    witness [p], Crane cannot express it in C++'s static type system and erases
    it to [std::any].

    The bug: at the *construction* site Crane stored the function by wrapping the
    raw lambda closure directly into the [std::any] (so the [std::any] held the
    closure type), but at the *application* site it retrieves the function with
    [std::any_cast<std::function<std::any(std::any)>>]. Those two representations
    disagreed, so the cast threw [std::bad_any_cast] at runtime — even though the
    Rocq program is perfectly well typed and total.

    The fix wraps a non-lambda function value stored into an erased field with
    the [crane_erase_fn] runtime helper, which adapts the callable to the
    canonical [std::function<std::any(std::any...)>] representation the
    application site expects.

    This file distills that pattern to its essence. *)

(** Abstract semantic-type family, mirroring parse-a-lot's [nt_semty]. *)
Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

Module Make (S : SEM).

  (** [production]-analog: an index plus a list of indices. *)
  Definition prod2 : Type := (S.idx * list S.idx)%type.

  (** [predicate_semty]-analog: a value-dependent function type. The
      [let (a, _) := p] blocks reduction for a variable [p], so Crane must erase
      [pred_ty p] to [std::any] — exactly like [predicate_semty] in Defs.v. *)
  Definition pred_ty (p : prod2) : Type :=
    let (a, _) := p in S.sem a -> bool.

  (** [grammar_entry]-analog: a dependent pair carrying the function payload. *)
  Definition entry : Type := { p : prod2 & pred_ty p }.

  (** Build an entry from a concrete index and a predicate lambda.
      The lambda is stored at the erased type [pred_ty (a, [])] = [std::any]. *)
  Definition mk (a : S.idx) (f : S.sem a -> bool) : entry :=
    existT pred_ty (a, []) f.

  (** Look up + apply: destructure the entry and apply the stored predicate.
      Here the projected [f] has C++ static type [std::any], so Crane emits
      [any_cast<std::function<...>>(f)(...)] — the failing cast. *)
  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) f => if f (arg a) then true else false
    end.

End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => nat.
End Inst.

Module M := Make Inst.

Definition my_entry : M.entry := M.mk tt (fun n => Nat.eqb n 0).
Definition my_arg   : forall a : Inst.idx, Inst.sem a := fun _ => 0.

(** In Rocq this evaluates to [true] ((fun n => n =? 0) 0), and the extracted
    C++ now returns [true] as well.  Kept as a function (not a value) so the C++
    test driver can invoke it under try/catch (before the fix it threw
    [std::bad_any_cast]). *)
Definition check (u : unit) : bool := M.run my_entry my_arg.

Crane Extraction "sigt_fn_any" check my_entry my_arg.
