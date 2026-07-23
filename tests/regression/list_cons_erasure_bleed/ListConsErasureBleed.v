From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(** Regression test (now fixed). This mirrors [theories/Parser/Defs.v]'s
    [concat_tuple]/[rev_tuple] family verbatim (same tactic-built
    dependent-case-split style, same
    [symbols_semty gamma := tuple (map symbol_semty gamma)] domain), with
    [sym] standing in for [symbol]. [rev_tuple_cons_case] calls
    [concat_tuple (rev xs') [x] (f xs' vs) (v, tt)] -- where [[x] : list sym]
    is a concrete singleton grammar-symbol list built in the SAME function
    that also builds the erased singleton value tuple
    [(v, tt) : syms_semty [x]]. [check] forces [rev_tuple] on a two-element
    list so Crane must extract [rev_tuple_cons_case] for real.

    Three bugs were fixed in [src/translation.ml]'s [gen_expr_custom_cons]
    (the custom-cons codegen for [prod]/[list]) and [gen_custom_cpp_case]:

    1. [flows_into_erased_slot] boxed a constructor argument into [std::any]
       whenever the ENCLOSING function's return type resolved to [std::any],
       even when the argument being built was an unrelated CONCRETE value
       (e.g. the singleton list [[x] : list sym] built inside a function
       that separately returns an erased [syms_semty]). This produced
       [std::any(x)] passed to the list's [push_front], which only accepts
       a concrete [Sym] -- "no matching member function for call to
       'push_front'". Fixed by excluding list-cons constructors from
       [flows_into_erased_slot] (the boxing is only meaningful for
       pair/tuple constructors).

    2. Even after (1), matching on [rev_tuple]'s result in [check] crashed at
       runtime with [std::bad_any_cast]. [rev_tuple]'s Rocq-level type
       ([forall xs, syms_semty xs -> syms_semty (rev xs)]) is a single
       generic C++ function whose return type is the value-dependent-erased
       [syms_semty] ([std::any]) -- but Rocq's type-checker concretely
       reduces the call-site type ANNOTATION for a literal list argument
       (e.g. [[A; B]]), making [gen_custom_cpp_case] believe the match
       scrutinee was concretely typed and skip the [any_cast<pair<any,any>>]
       needed to safely destructure it. Fixed by adding
       [scrut_callee_ret_erased], which looks up the callee's UN-INSTANTIATED
       type scheme via [find_type_opt] (rather than relying solely on the
       call-site-reduced annotation) to detect the erasure, together with a
       [flatten_app] helper that strips curried [MLapp] nesting and
       [MLmagic]-wrapped callee heads so the callee's [MLglob] head can be
       recovered.

    3. Once (1) and (2) compiled cleanly, a further [std::bad_any_cast]
       surfaced at runtime: the literal pair value [(n, (n, tt))] passed as
       an argument to [rev_tuple] (whose parameter type is the erased
       [syms_semty]) was boxed as a single [std::any] holding the full
       CONCRETE nested pair, instead of being erased component-by-component
       to match what generic consumers (e.g. [rev_tuple_cons_case]'s
       [any_cast<pair<any,any>>]) expect at every nesting level -- and the
       same issue affected pair literals built INSIDE a custom-cons's own
       fields (e.g. [(v, tt)] in [rev_tuple_cons_case], where [v] is itself
       already read out of an erased slot via [any_cast]). Fixed by (a)
       propagating the erased-return-slot context into nested prod-cons
       fields instead of resetting it, so a nested pair also self-boxes its
       own components, and (b) narrowing the "already erased, don't re-box"
       guard in [gen_expr_custom_cons] from "any [CPPany_cast]" to
       specifically "[CPPany_cast (Tany, _)]", since an [any_cast] to a
       CONCRETE type (e.g. [any_cast<uint64_t>(s)]) still produces a raw,
       un-boxed value that must be re-boxed to flow into a [pair<any,any>]
       slot. *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive sym := A | B.
Definition sym_semty (s : sym) : Type := nat.
Definition syms_semty (g : list sym) : Type := tuple (map sym_semty g).

Definition concat_tuple_nil_case :
  forall (xs ys : list sym)
         (vs    : syms_semty xs)
         (vs'   : syms_semty ys)
         (heq   : xs = []),
    syms_semty (xs ++ ys).
  intros xs ys vs vs' heq; subst; auto.
Defined.

Definition concat_tuple_rec_case :
  forall (x         : sym)
         (xs' xs ys : list sym)
         (vs        : syms_semty xs)
         (vs'       : syms_semty ys)
         (f         : forall xs ys, syms_semty xs -> syms_semty ys -> syms_semty (xs ++ ys))
         (heq       : xs = x :: xs'),
    syms_semty (xs ++ ys).
  intros x xs' xs ys vs vs' f heq; subst; simpl in vs.
  destruct vs as (v, vs).
  simpl; constructor.
  - exact v.
  - apply f; auto.
Defined.

Fixpoint concat_tuple
           (xs ys : list sym)
           (vs    : syms_semty xs)
           (vs'   : syms_semty ys) : syms_semty (xs ++ ys) :=
  match xs as xs' return xs = xs' -> _ with
  | []       => fun heq => concat_tuple_nil_case xs ys vs vs' heq
  | x :: xs' => fun heq => concat_tuple_rec_case x xs' xs ys vs vs' concat_tuple heq
  end eq_refl.

Definition rev_tuple_nil_case :
  forall (xs : list sym) (vs : syms_semty xs) (heq : xs = []),
    syms_semty (rev xs).
  intros; subst; auto.
Defined.

Definition rev_tuple_cons_case :
  forall (xs  : list sym)
         (x   : sym)
         (xs' : list sym)
         (heq : xs = x :: xs')
         (vs  : syms_semty xs)
         (f   : forall xs, syms_semty xs -> syms_semty (rev xs)),
    syms_semty (rev xs).
  intros xs x xs' heq vs f; subst; simpl in vs.
  destruct vs as (v, vs).
  exact (concat_tuple (rev xs') [x] (f xs' vs) (v, tt)).
Defined.

Fixpoint rev_tuple (xs : list sym) (vs : syms_semty xs) : syms_semty (rev xs) :=
  match xs as xs' return xs = xs' -> _ with
  | []       => fun heq => rev_tuple_nil_case xs vs heq
  | x :: xs' => fun heq => rev_tuple_cons_case xs x xs' heq vs rev_tuple
  end eq_refl.

Definition check (n : nat) : nat :=
  match rev_tuple [A; B] (n, (n, tt)) with (v, _) => v end.

Crane Extraction "list_cons_erasure_bleed" check.
