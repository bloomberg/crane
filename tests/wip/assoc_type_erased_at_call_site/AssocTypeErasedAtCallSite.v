(* A caller spells a promoted associated type without consulting the instance
   it just named.

   [@ptr (@PointerV IPZ)] is a closed type: the instance is written right
   there, so the caller has everything it needs to spell
   [PointerV<IPZ>::ptr].  It does not, and falls back to the file-scope
   [using ptr = std::any] the {e class} declares -- while the callee's own
   signature, generated on the function path, resolved the same type through
   its parameter.

   This is the third disagreement in the family, after the arity gap at a use
   site and the body/signature split inside one instance
   ([assoc_type_erased_in_body]).  Both of those are fixed; this one is
   between two declarations that never meet in one struct.

   The reduction takes two parameters of the same Rocq type on purpose.  On
   Vellvm the two are spelled differently {e within one signature} --
   [const std::pair<Nat, std::optional<List<Nat>>> &a] beside [ptr b] -- the
   only visible difference being [const&] against by-value, and a third
   occurrence arrives wrapped in [crane_any_cast].  So "the caller does not
   consult the instance" is too strong as a statement of the defect: something
   consults it for some positions.  Naming the discriminator is the point of
   the test.

   [tag_of] projects [b] rather than ignoring it.  With both parameters unused
   the reduction is green: [std::any] absorbs the pair the caller passes, so
   the two spellings never have to agree.  A reduction made only of absorbing
   types cannot report a carrier defect -- the erased parameter has to be read
   back at its real type for the disagreement to have anywhere to show.

   Where it is not: the instance argument is gone before the C++ side sees
   anything.  [translation.ml]'s promoted-type-var case receives
   [Tglob (ptr, [])] -- [nts=0] on every one of 48 occurrences, all taking the
   identical branch -- so [gen_decls] has nothing to resolve through and the
   file-scope alias is the only answer left.  Naming this a call-site defect in
   the C++ generator is therefore wrong; by then the information is already
   destroyed.

   Where it is: [extract_type]'s [Const]/[TypeScheme] case in
   [extraction.ml:599].  It [whd_all]s a promoted projection applied to
   arguments, and rejects the result as [is_stuck] when it is a [Case] -- which
   is what the eliminator of a non-primitive record reduces to.  One domain per
   function comes back stuck and keeps [Tglob ptr]; the others reduce to
   [(iptr * prov)].  The pattern is structural, not positional-first: with
   three parameters of this type the first two reduce and the third does not,
   and with one parameter that one does not.  It is always the innermost arrow.

   Not yet explained: why the innermost arrow's domain reduces differently from
   its siblings when the Rocq term is the same in all of them.  The stuck
   reduction reports its scrutinee as the bare class [PTR] rather than
   [@PointerV IPZ], so something is reaching [whd_all] without the instance
   substituted, and until that is known the fix cannot be chosen -- relaxing
   [is_stuck] to accept a [Case] would change all of them, and a perturbation
   that moves every occurrence is evidence about none. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class IPtr := { iptr : Set ; zero_iptr : iptr }.

#[global] Instance IPZ : IPtr := { iptr := nat ; zero_iptr := 0 }.

Definition prov : Set := list nat.
Definition nil_prov : prov := nil.

Class PTR := { ptr : Set ; null : ptr ; ptr_tag : nat }.

#[global] Instance PointerV {IP : IPtr} : PTR :=
  { ptr := (iptr * prov)%type ; null := (zero_iptr, nil_prov) ; ptr_tag := 7 }.

Module AssocTypeErasedAtCallSite.

  (** Both parameters have the same Rocq type, written at a named instance. *)
  Definition tag_of (a : @ptr (@PointerV IPZ)) (b : @ptr (@PointerV IPZ)) : nat :=
    fst b.

  Definition go (_ : nat) : nat :=
    tag_of (@null (@PointerV IPZ)) (@null (@PointerV IPZ)).

End AssocTypeErasedAtCallSite.

Crane Extraction "assoc_type_erased_at_call_site" AssocTypeErasedAtCallSite.
