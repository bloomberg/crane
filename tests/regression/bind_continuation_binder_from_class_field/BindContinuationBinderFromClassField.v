(** The {e element} half of Vellvm Cluster A --- h:40336, h:40344, h:40348 ---
    as distinct from the three {e codomain} sites covered by
    [tests/wip/inner_fix_codomain_from_class].  Six bare [typename _tcI0::IPTR]
    in [MemoryBytes.memory_bytes_to_dvalue] split 3/3 by position:

    {v
      40281  std::function<typename _tcI0::IPTR(          codomain
      40295  -> typename _tcI0::IPTR {                    codomain
      40358  -> typename _tcI0::IPTR {                    codomain
      40336  [=](typename _tcI0::IPTR f) mutable {        ELEMENT   <-- here
      40344  [=](List::list<typename _tcI0::IPTR> rest)   ELEMENT   <-- here
      40348  List::template list<typename _tcI0::IPTR>::cons(       ELEMENT
    v}

    The codomain account does not reach these, and the artifact decides it
    rather than an argument.  [bind<A, B>]'s continuation takes an [A], and [A]
    is spelled out {e correctly} two lines above the binder that gets it wrong:

    {v
      ::EOU_monad::template bind<
          Dvalue<typename _tcI0::PTR::ptr, typename _tcI0::IPTR::iptr>,
          List::list<Dvalue<..., ...>>>(
          MemoryBytes::template memory_bytes_to_dvalue<_tcI0>(...),
          [=](typename _tcI0::IPTR f) mutable {          // f must be Dvalue<...>
    v}

    At 40344 the outer [List::list] is right and only the {e leaf} is erased,
    which rules out a whole-type substitution: something wrote the correct
    constructor around the wrong argument.  And unlike the codomain half, this
    one has a source you can name --- the element type is [dv], an ordinary
    class-parameterised inductive, not a type field of any class, and it is
    present in the [bind] call's own type arguments.  If it is still lost at the
    binder, it was dropped rather than never held.

    {b The control is inside the reduction, not beside it.}  The two [bind]
    continuations below are over the same element type in the same emitted
    function, one inside the inline [fix] and one outside it:

    {v
      inside   [=](List<typename _tcI0::addr> r) mutable {        WRONG
      outside  [](const List<Dv<typename _tcI0::addr>>& r) {      RIGHT
    v}

    Every variable a sibling control would have to hold constant --- the class,
    the monad instance, the element type, the plugin revision, the flags --- is
    held here by identity rather than by assertion, because the two sites are
    eleven lines apart in one function.

    {b Hypothesis, stated as one, before any fix exists:} [f] and [r] are the
    erased binders and [cons]'s argument type is merely inferred from them, so
    the element half is {e one} hole with two cascade sites, not three.  Not
    established.  Written down so that a 3 -> 0 is not read afterwards as three
    separate fixes landing.

    Four features of the Vellvm site are kept because it is not yet known which
    is load-bearing: an enclosing [Fixpoint] parameterised by a class; an inner
    [fix] that calls it, which is what keeps it inline rather than lifted (see
    [tests/regression/inline_inner_fix_writes_instance]); two {e nested} binds,
    the inner binder being a [list] of the element; and an element type built
    from a field of the class without being a class field itself.  The last is
    the first one to drop when narrowing.

    Reduced by the Vellvm-side session; ported here unchanged in substance from
    [src/crane/reductions/bind_continuation_binder_from_class_field].

    {b The h:40336 attribution above was withdrawn by its author and is kept
    only as the record of a near-miss.}  The reading it rests on --- that the
    wrong spelling is [Dv<A>] with the head dropped and the argument kept ---
    is an artefact of this file, where [addr] is simultaneously [Dv]'s first
    argument and a field of [Params], so the two readings are indistinguishable;
    widening [dv] to two fields does not separate them either.  In Vellvm the
    element is [Dvalue<_tcI0::PTR::ptr, _tcI0::IPTR::iptr>] and the binder
    writes [_tcI0::IPTR], which is neither argument nor head.  A reduction that
    matches an artifact's text is not one that matches its derivation.

    {b What probing this file does establish, and it points back at h:40336 by a
    different route.}  Neither wrong binder is a substitution at all.  Both end
    as an {e unresolved} type: the outer binder [f] as a bare ML type variable,
    the inner binder [r] as [list] of an uninstantiated [Tmeta].  A later pass
    fills such a position with the enclosing scope's promoted type variable ---
    which is [_tcI0::addr] here and would be [_tcI0::IPTR] in Vellvm, with no
    need for either to be an argument of anything.  On that reading the element
    half is not a second defect but the same filling as the codomain half,
    landing in a binder instead of a return type.  Stated as a hypothesis; what
    is measured is only the two unresolved positions.

    Two facts from the offer machinery ([Mlutil.recover_erased_types]), both
    reproducible and neither yet explained:

    - The continuation position {e is} offered the declared domain --- the
      offers for [bind] come out [T;-;T], so nothing is withdrawn there --- but
      the offer for [f] is the declaration's own type variable, uninstantiated.
      [bind] is called with three type arguments against a four-quantifier
      scheme, and a substitution that does not reach [A] offers a variable in
      its place.  An offer that is present and vacuous, not absent.

    - The inner binder is offered [list<dv>] against [list<Tmeta>] {e twice},
      with identical [have] and identical [from], and takes it once and declines
      it once.  Two passes run over the same body ([Gen_decls], [~only] being
      [names_promoted_type_var] then [writable_offer]), and the first declines
      what the second accepts, so this pair is expected rather than anomalous.

    {b What the types are by the time the lambda is built.}  Probing the
    parameter site in [Translation] gives three lambdas over the same Rocq type:

    {v
      ml=addr                 <- outer binder [f]
      ml=list, 0)[addr]       <- inner binder [r]
      ml=list, 0)[dv,  0)]    <- the control lambda, outside the fix
    v}

    So the wrong binders do not reach the printer unresolved after all.  By this
    point they hold [Tglob addr] --- the class {e field}, as an ML type --- and
    the recovery's own answer, [list<dv>], survives only in the control.
    Something between [Mlutil.recover_erased_types] and here overwrites the two
    positions inside the [fix] and leaves the one outside it alone.

    The account that covers this and the Vellvm census together: the binder's
    [Tmeta] and the [fix]'s codomain hole are the {e same cell}.  Filling a
    shared cell reaches every position that shares it, so one filler writes one
    spelling into structurally unrelated positions --- which is exactly what the
    artifact shows, fourteen defective sites all spelling [typename _tcI0::IPTR]
    where the lost types include both [Dvalue<ptr,iptr>] and
    [EOU<List<Dvalue<ptr,iptr>>>].

    {b That account is refuted.}  Logging every unification that writes a
    promoted type variable into a meta gives {e three distinct cells}:

    {v
      PROBE-MGU meta#3  := addr
      PROBE-MGU meta#26 := addr
      PROBE-MGU meta#28 := addr
    v}

    Three separate writes, not one write reaching three positions.  {b Both that
    reading and the shared-cell reading it replaced are void}: reordering the
    class's fields so the emitted filler becomes [tag] leaves every [mgu] write
    still saying [addr].  The writes are the legitimate pattern binders of
    [DAddr : addr -> dv P] in the synthesised [dv] conversion function.  They
    carried the spelling being hunted and nothing else.

    The probe was the problem, not the reading of it.  It read an internal event
    on one input; an account that cannot be made to move with the output has not
    been tested against anything.  Any further probe here must be differential by
    construction --- reorder the class fields and require the instrumented value
    to move from [addr] to [tag].

    {b The site, found by that probe and passing that criterion.}  It is
    [Gen_decls.rewrite_ml_ast_types], and it has described itself all along:

    {v
      let carrier_ref = fst (List.hd carrier_refs) in
      let rec rty t = match t with
        | Tunknown -> Tglob (carrier_ref, [], [])
        | Tmeta {contents = None} -> Tglob (carrier_ref, [], [])
        ...
    v}

    Every empty annotation in the body is replaced by {e one} globref, and
    [carrier_refs] is sorted so its head is the class's first-declared
    associated type.  Its own docstring says so --- "the carrier is a guess and
    can only be one: every hole in the body is filled with the same associated
    type, so a class declaring three of them spells whichever one heads the
    list at all three".  The defect is not a wrong answer; it is a guess
    running where no answer was available, and the artifact is what that guess
    looks like when the holes are not the carrier.

    Instrumented, it fires 28 times in this file, every one of them naming
    [addr]; reorder [Params] to put a [tag] field first and all 28 name [tag],
    moving with the emitted filler.  That is the acceptance criterion the
    voided probes could not meet.

    The lift asymmetry falls out of the same site: a lifted helper's codomain
    is a real type variable in its own template head, not a [Tmeta] or a
    [Tunknown], so [rty] does not match it and nothing is filled --- which is
    exactly the undeducible parameter
    [tests/wip/inner_fix_codomain_from_class] shows.  One guess, two outcomes,
    decided by whether the hole survived as a hole.

    {b What the fix is not.}  [recover_then_guess] runs
    [Mlutil.recover_erased_types] first so the declaration can name the holes
    it can, and the guess is meant to see only the rest.  Making the recovery
    {e write the cell} it accepts --- so a recovered answer reaches every
    position sharing that metavariable, rather than only the occurrence asked
    about --- is a real improvement and is {e not} this fix: it leaves all 28
    fills in place, because the recovery is never offered anything for these
    holes in the first place.  Measured, not assumed.

    {b What declining costs, measured over the whole corpus.}  Disabling
    [rewrite_ml_ast_types] outright and re-extracting all 1022 tests changes
    {e three} generated files: [monadic/stmonad], [regression/double_opposite_witnesses]
    and this one.  Both of the others still pass, [dune build @runtest] is
    identical to its baseline (the one [stmonad] benchmark failure is
    pre-existing and reproduces with the guess in place), and basics and
    monadic are green.  Nothing in the corpus depends on the guess being right.

    The Vellvm-side session measured the same question at the artifact, by
    substituting [std::any] at each of the 14 defective sites and recompiling:
    eleven of them --- all of Cluster B and all three element sites --- accept
    erasure with {e no} change to the error multiset.  The cost is exactly the
    three inline-[fix] codomains, which are the positions where there is
    nothing to decline {e to}: the carrier is a type field of the monad class
    and MiniML cannot express it.  So the guess is not a trade-off, it is a
    partition, and only the codomain third needs an answer supplied rather
    than withheld.

    {b Declining is necessary here and not sufficient.}  With the guess off,
    every element position in this test is spelled correctly
    ([Dv<typename _tcI0::addr> f], [List<Dv<...>>] at the leaf and at [cons]).
    The test still fails, on two defects the guess was masking: the [fix] is
    now {e lifted} --- the annotations it turned on have changed --- and the
    lifted helper is called as [bytes_to_dv<_tcI0>(k, bs0)] with [k] a free
    variable it never received.  A separate defect, in the same family as
    [tests/regression/inline_inner_fix_writes_instance]; noted here so the
    remaining diagnostics are not read as the filler surviving.

    This also withdraws the prediction the shared-cell account licensed --- that
    the defective sites cannot be fixed in groups.  On three independent cells
    they can be, so a partial fix is not evidence of anything either way.

    {b The fix, in three parts, and why the first of them is not optional.}

    - {e The guess is deleted, not bypassed.}  [Gen_decls.rewrite_ml_ast_types]
      and its support are gone.  The measurement above shows declining is
      affordable; what makes deletion {e mandatory} is ordering: [Gen_decls]
      runs before [Translation], so with the guess in place it fills the same
      shared cells with [addr] first and the recovery below never sees a hole
      to fill.  The guess does not merely duplicate a later pass, it pre-empts
      it.  Re-enabling it reproduces [-> typename _tcI0::addr] exactly.

    - {e The codomain is recovered from the term.}  [recover_fix_codomain]
      already claimed to do this and missed on two axes, both of which apply
      here: it matched only an already-minted [Tvar] codomain and not a
      [Tmeta {contents = None}], and its tail reader recognised only an
      [MLcons] tail and not an application.  Widening both, plus a new
      [ml_app_result_type] that instantiates a callee's declared codomain the
      way [gen_app]'s [subst_ml_ty] instantiates its domains (the call's own
      type arguments, then the dictionary's carrier), answers it.  Filling the
      [Tmeta] cell {e is} the substitution --- see
      [[fill-the-hole-not-the-type]].

    - {e The lifted [fix] gets closure conversion.}  There are two lift paths
      in [Translation] and only the lifted-{e lambda} one ever had it; the
      [MLletin (_, _, MLfix ...)] path lifted a body out of the scope that
      bound its free variables and left every call unchanged, which is the
      [k]-never-received defect noted above.  The lambda path's conventions
      are reused rather than re-invented.  One exclusion is load-bearing: a
      class instance is {e not} a free value.  [current_class_temps] already
      carries [_tcI0] as a template parameter explicit at every reference, and
      passing it again emits [const Params _tcI0], shadowing its own template
      parameter.

    With all three the [fix] is inline again and every position is correct. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(** Carrier and monad, reached through an ExtLib [Monad] {e instance}, as
    Vellvm reaches them. *)
Inductive EOU (A : Type) : Type :=
| Ok : A -> EOU A
| Err : nat -> EOU A.

Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end
  |}.

Class Params := { addr : Type ; zero : addr }.

(** The element type: class-parameterised, but an ordinary inductive and {e not}
    a type field of any class.  This is the difference from the codomain half. *)
Inductive dv (P : Params) : Type :=
| DAddr : addr -> dv P
| DNum : nat -> dv P.

Arguments DAddr {P}.
Arguments DNum {P}.

Inductive byte (P : Params) : Type :=
| B : nat -> byte P.

Arguments B {P}.

Fixpoint bytes_to_dv {P : Params} (n : nat) (bs : list (byte P)) : EOU (dv P) :=
  match n, bs with
  | O, _ => ret (DNum 0)
  | S k, nil => ret (DAddr zero)
  | S k, cons (B v) rest =>
      (* The inner [fix] calls the enclosing [Fixpoint], so it stays inline. *)
      let fix go (ds : list nat) (bs0 : list (byte P)) : EOU (list (dv P)) :=
          match ds with
          | nil => ret nil
          | cons _ ds' =>
              (* Outer bind: the continuation binder must be [dv P].  Vellvm
                 h:40336 writes the class instance here. *)
              bind (bytes_to_dv k bs0)
                   (fun (f : dv P) =>
                      (* Nested bind: the binder must be [list (dv P)], and in
                         the artifact the outer [list] is correct while the
                         LEAF is erased.  Vellvm h:40344, h:40348. *)
                      bind (go ds' bs0)
                           (fun (r : list (dv P)) => ret (cons f r)))
          end
      in
      (* The control arm: the same element type, the same monad, outside the
         inline [fix].  This one is spelled correctly. *)
      bind (go (cons v nil) rest) (fun r => ret (DNum (length r)))
  end.

#[global] Instance natParams : Params := {| addr := nat ; zero := 0 |}.

Module BindContinuationBinderFromClassField.
  Definition run : EOU (dv natParams) :=
    @bytes_to_dv natParams 2 (cons (B 1) nil).
End BindContinuationBinderFromClassField.
Crane Extraction "bind_continuation_binder_from_class_field" BindContinuationBinderFromClassField.
