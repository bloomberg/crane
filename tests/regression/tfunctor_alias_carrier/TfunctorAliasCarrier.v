(** Crane bug: [tfmap] at a carrier that is a type *alias*
    ([texp T := T * exp T]) passes the alias template bare as the carrier.

    Observed (e888c04f0), in [TFunctor_cmpxchg]:
      tfmap<TfunctorAliasCarrier::texp, std::any, std::any>(..., c.c_ptr)
    [tfmap]'s first template parameter is a plain [typename T1] (the
    carrier at the current instantiation), so it should be
    [texp<std::any>].  (The [exp] field just above gets
    [tfmap<exp<std::any>, std::any, std::any>], correctly.)  Diagnostic:
      error: no matching function for call to 'tfmap'
      note: candidate template ignored: invalid explicitly-specified
            argument for template parameter 'T1'

    Reduced from Vellvm, [Syntax/LLVMAst.v:516]
    ([Definition texp : Set := T * exp]) and [Syntax/Traversal.v:591]
    [TFunctor_texp], used by [TFunctor_cmpxchg] etc.:
    [Traversal::template tfmap<texp, std::any, std::any>(h4, f, c.c_ptr)]
    (28 errors on e888c04f0, most of what is left). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module TfunctorAliasCarrier.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  Section Syntax.
    Variable T : Set.
    Inductive exp : Set := Lit (t : T) | Neg (e : exp).
    (* Vellvm's LLVMAst: [Definition texp : Set := T * exp.] *)
    Definition texp : Set := (T * exp)%type.
    Record cmpxchg : Set := mk_cmpxchg { c_ptr : texp ; c_new : texp }.
  End Syntax.
  Arguments Lit {T}. Arguments Neg {T}.
  Arguments mk_cmpxchg {T}. Arguments c_ptr {T}. Arguments c_new {T}.

  #[global] Instance TFunctor_exp : TFunctor exp :=
    fix go U V f e := match e with Lit t => Lit (f t) | Neg e' => Neg (go U V f e') end.

  #[global] Instance TFunctor_texp `{TFunctor exp} : TFunctor texp :=
    fun _ _ f '(t, e) => (f t, tfmap f e).

  (* Traversal.v's [TFunctor_cmpxchg]: fields of alias type [texp]. *)
  #[global] Instance TFunctor_cmpxchg : TFunctor cmpxchg :=
    fun U V f c => mk_cmpxchg (tfmap f (c_ptr c)) (tfmap f (c_new c)).

  Definition c0 : cmpxchg nat := mk_cmpxchg (1, Lit 1) (2, Neg (Lit 2)).
  Definition c1 : cmpxchg nat := tfmap S c0.
  Definition is_five : bool := Nat.eqb (fst (c_ptr c1) + fst (c_new c1)) 5.
End TfunctorAliasCarrier.

Crane Extraction "tfunctor_alias_carrier" TfunctorAliasCarrier.
