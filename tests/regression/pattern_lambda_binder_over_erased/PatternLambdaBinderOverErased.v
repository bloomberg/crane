(* A pattern lambda mapped over a list of pairs, where the binder's own ML
   type erases a component the container keeps.  It used to be spelled

     [=](std::pair<Nat, std::any> ie) mutable { const auto& [i, e] = ie; ... }

   against a [List<std::pair<Nat, Exp0<std::any>>>], and both errors followed
   from that one disagreement: [e] destructured as [std::any], so the inner
   [tfmap(h, f, e)] could not match [T1<T2>] against it, and the lambda was
   therefore not invocable on the real element type, killing the enclosing
   [tfmap<List>] with a substitution failure.

   Nothing was lost in translation -- the binder's ML type carries an
   unresolved [Tmeta] in that component, so it was never inferred at all.  The
   shape is only knowable from the slot the lambda flows into, whose domain
   the callee declares as [std::pair<Nat, Exp0<T1>>].  A type variable this
   lambda cannot name is one the caller's erasure already dropped, so [T1]
   erases to [std::any] and the rest of the slot's spelling stands.

   Two things this is NOT, each of which took an extraction round to rule out.
   It is not the higher-kinded carrier: [dict_carrier_type_args] handles the
   dictionary-as-parameter shape correctly, and with the element typed rather
   than erased the same code came out as [tfmap<Exp0>(h, f, ie.second)] and
   compiled.  And it needs a {e pattern} lambda: written point-free as
   [fun ie => (fst ie, tfmap f (snd ie))] the binder comes out [const auto&]
   and there is nothing to disagree with.

   Vellvm: vellvm_bench.cpp:5191 and 5197, with the same two diagnostics down
   to the notes, plus eight siblings across [TFunctor_phi], [TFunctor_code]
   and [TFunctor_block] in rocq/Syntax/Traversal.v -- the largest cluster in
   that extraction (10 of 28). *)

From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.

Class TFunctor (T : Set -> Set) :=
  tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

Inductive exp (T : Set) : Set := Var (t : T) | Lit (n : nat).
Arguments Var {T}.
Arguments Lit {T}.

#[global] Instance TFunctor_list : TFunctor list := fun U V f l => List.map f l.

#[global] Instance TFunctor_exp : TFunctor exp :=
  fun U V f e => match e with Var t => Var (f t) | Lit n => Lit n end.

Inductive phi (T : Set) : Set := Phi (es : list (nat * exp T)).
Arguments Phi {T}.

(** The shape under test.  The [exp] instance is a hypothesis rather than a
    resolution, which is what makes the inner call's failure visible as a
    deduction failure instead of a silent mis-instantiation. *)
Section WithExp.
  Context `{h : TFunctor exp}.

  #[global] Instance TFunctor_phi : TFunctor phi :=
    fun U V f p => match p with Phi es => Phi (tfmap (fun ie : nat * exp U => let (i, e) := ie in (i, tfmap f e)) es) end.
End WithExp.

Module PatternLambdaBinderOverErased.

  Definition bump (n : nat) : nat := S n.

  Definition on_phi (p : phi nat) : phi nat := tfmap bump p.

End PatternLambdaBinderOverErased.

Crane Extraction "pattern_lambda_binder_over_erased" PatternLambdaBinderOverErased.
