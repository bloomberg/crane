(** Crane bug: a natural transformation's codomain becomes a template
    template parameter that appears only in the return type, so no call to it
    can ever be resolved.

    [case_] takes [f : E ~> M] and [g : F ~> M] and produces [E +' F ~> M].
    [M] is a type constructor, so Crane makes it a template template parameter
    [T3], and [T3] occurs only in the return type and in the [requires]
    clause -- never in a function parameter:

      template <template <typename> class T1, template <typename> class T2,
                template <typename> class T3, typename T4,
                typename F0, typename F1>
        requires std::is_invocable_r_v<T3<std::any>, F0 &, T1<std::any> &> &&
                 std::is_invocable_r_v<T3<std::any>, F1 &, T2<std::any> &>
      static T3<T4> case_(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab);

    The handlers [f] and [g] are passed as generic lambdas, which carry no
    information about their return type, and the call site supplies no
    explicit template arguments:

      return Handler::case_([](const auto &e) { ... },
                            [](const auto &b) { ... }, ab);

    Expected: the call site to name the carrier, e.g.
              [Handler::case_<ReqA, ReqB, std::optional>(...)], or the
              handlers to be emitted with a concrete return type.
    Actual:   error: no matching function for call to 'case_'
              note: candidate template ignored: couldn't infer template
                    argument 'T3'

    Seen in Vellvm wherever ITree's [case_] / [Handler] combinators are used;
    six call sites in the extracted interpreter fail this way.

    Vellvm also shows a second, unreduced defect on the same combinator: the
    scrutinee's type is printed with no name at all,

      std::get<typename<T1<std::any>, T2<std::any>, T4>::Inl1>(ab.v())

    which this reduction does not trigger -- here [Sum1] is spelled
    correctly. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsWIP Require undeducible_tt_return.Sum.
From CraneTestsWIP Require undeducible_tt_return.Handler.

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
