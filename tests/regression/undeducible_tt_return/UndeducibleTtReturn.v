(** A natural transformation's codomain is a type constructor the caller
    chooses, and nothing in the call's arguments names it.

    [case_] takes [f : E ~> M] and [g : F ~> M] and produces [E +' F ~> M].
    [M] becomes a template template parameter, and it occurs only in the
    return type -- never in a value parameter -- so a call site can neither
    supply it nor have it deduced.  What does pin it is the handler: [f] is a
    polymorphic function object, so [std::invoke_result_t<F0 &, T1<T4> &>] is
    [M X] at this very instantiation, and the parameter is dropped:

      template <template <typename> class T1, template <typename> class T2,
                typename T4, typename F0, typename F1>
      static std::invoke_result_t<F0 &, T1<T4> &>
      case_(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab);

    The handlers are the other half of the same story.  Each is rank-2 -- a
    [forall X] extraction hands over as [Tunknown] -- and is emitted as a
    lambda with a template parameter of its own, so the erased position is a
    type the call deduces rather than a [std::any] the body has to guess:

      []<typename _X>(const ReqA<_X> &e) { ... }

    The [requires] clauses go with the template template parameter they were
    written in terms of: [std::is_invocable_r_v<T3<std::any>, F0 &, ...>] is
    not a weaker statement of the handler's type but a false one, since the
    body applies [f] at the function's own [X].

    Reduced from Vellvm, where ITree's [case_] and [Handler] combinators are
    used at six call sites that all failed this way. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require undeducible_tt_return.Sum.
From CraneTestsRegression Require undeducible_tt_return.Handler.

Variant reqA (X : Type) : Type := mkA (x : X).
Variant reqB (X : Type) : Type := mkB (x : X).
Arguments mkA {X}.
Arguments mkB {X}.

Module UndeducibleTtReturn.
  Definition use (ab : Sum.sum1 reqA reqB nat) : option nat :=
    Handler.case_ (E := reqA) (F := reqB) (M := option)
      (fun _ e => match e with mkA x => Some x end)
      (fun _ b => match b with mkB x => Some x end) _ ab.
End UndeducibleTtReturn.

Crane Extraction "undeducible_tt_return" UndeducibleTtReturn.
