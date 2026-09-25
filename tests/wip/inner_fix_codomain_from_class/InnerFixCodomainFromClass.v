(** An unannotated [let]-bound inner [fix] whose every branch returns through a
    {e monad class method} rather than a concrete constructor.  Nothing in the
    body pins the codomain: [mret] has type [forall A, A -> M A] for the class
    variable [M], so the branch types say only "the carrier, at [list dv]", and
    the codomain of the [fix] is left as a type variable of its own.

    Here that variable reaches the lifted helper's template head, where it is
    undeducible --- it occurs in none of the helper's parameters, only as the
    {e return type} of the lambda the helper returns:

    {v
      template <Params _tcI0, typename T2>
      auto _collect_go_all(const std::optional<Nat> pad) {
        auto go_impl = [=](auto &_self_go, auto m, List<dv<...>> ys) mutable -> T2 {
      ...
      _collect_go_all<_tcI0>(std::optional<Nat>())(n, xs);   // cannot infer T2
    v}

    [generalize_lambda_only_tparams] declines it correctly, as it moves lambda
    {e binders} and this is a return type --- but the principle is the same one:
    the polymorphism belongs to the lambda, and a lambda return type that is
    undeducible from outside is one C++ can deduce for itself if simply left
    unwritten.

    The same undetermined codomain is behind Vellvm h:40291,
    [MemoryBytes.memory_bytes_to_dvalue], where the inner [fix] calls the
    enclosing [Fixpoint] and so stays inline instead of being lifted.  There the
    hole is not left open but {e filled}, with the enclosing class instance:

    {v
      std::function<typename _tcI0::IPTR(std::optional<N>, ...)>
        list_memory_bytes_to_dvalue = [=](...) mutable {
          auto go_impl = [&](...) -> typename _tcI0::IPTR {
            return ::EOU_monad::template ret<List::list<Dvalue<...>>>(...);
    v}

    One cause, two fillings, decided by whether the [fix] was lifted.  The
    neighbouring case that returns via a concrete constructor is correct and is
    pinned by [tests/regression/inline_inner_fix_writes_instance]: going through
    the class is what loses the codomain.

    {b What is known so far, so it is not re-derived.}

    - The hole is at the ML level, not the C++ one.  The let-binding's ML type
      is a chain of instantiated [Tmeta] cells ending at a genuinely {e free}
      type variable.  The carrier is a type {e field} of the monad class, which
      MiniML cannot express, so it erases to a free variable and there is
      nothing left in the ML type to recover it from.  Any repair has to come
      from the dictionary, not from [t].

    - Extending [generalize_lambda_only_tparams] to release a lambda's return
      {e annotation} --- deleting it rather than replacing it, so C++ deduces
      from the body, which does spell the type --- is the right shape and is
      {e not} sufficient on its own.  [T2] is additionally pinned by an
      occurrence in the type-argument list of the [mret] call, which the printer
      then truncates away.  So the analysis declines on an occurrence that never
      reaches the text.  Deciding that correctly means asking the same question
      the printer asks about which prefix it writes, and that is printer-side
      knowledge the lift does not currently have. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class IPtr := { iptr : Type; zero_iptr : iptr }.
Class Ptr := { ptr : Type; zero_ptr : ptr }.

(** Both fields are themselves instances, as [Params] is in Vellvm.  [IPTR] is
    the one Crane writes; it is the last field, and that is worth keeping in
    view when diagnosing how the hole is filled. *)
Class Params := { PTR :: Ptr; IPTR :: IPtr }.

(** A monad class, as Vellvm reaches [ret] through [ExtLib]'s. *)
Class MyMonad (M : Type -> Type) := {
  mret : forall {A}, A -> M A;
  mbind : forall {A B}, M A -> (A -> M B) -> M B
}.

Inductive EOU (X : Type) : Type :=
  | eou_err : EOU X
  | eou_ret : X -> EOU X.
Arguments eou_err {X}.
Arguments eou_ret {X} _.

#[global] Instance EOU_monad : MyMonad EOU := {|
  mret A x := eou_ret x;
  mbind A B c k := match c with eou_err => eou_err | eou_ret x => k x end
|}.

Section S.
  Context {Pa : Params}.

  Definition dv := (ptr * iptr)%type.

  Fixpoint collect (n : nat) (xs : list dv) : EOU dv :=
    (* Unannotated, as Vellvm leaves it.  Every branch returns through [mret]
       or [mbind], so the codomain is the class carrier and no branch says
       which type that is. *)
    let go_all (pad : option nat) :=
      fix go (m : nat) (ys : list dv) : _ :=
        match ys with
        | nil => mret (@nil dv)
        | cons y ys' =>
          mbind (go m ys') (fun rest =>
            if pad then mret (cons y rest) else mret rest)
        end
    in
    match xs with
    | nil => eou_err
    | cons x xs' =>
      match n with
      | O => match go_all None n xs with
             | eou_ret (cons z _) => mret z
             | _ => mret x
             end
      | S n' => collect n' xs'
      end
    end.
End S.

Module InnerFixCodomainFromClass.
  Definition use `{Pa : Params} (x : dv) : EOU dv := collect 0 (cons x nil).
End InnerFixCodomainFromClass.
Crane Extraction "inner_fix_codomain_from_class" InnerFixCodomainFromClass.
