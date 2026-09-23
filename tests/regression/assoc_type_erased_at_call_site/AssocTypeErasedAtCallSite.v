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

   Where it is: the guard in front of that reduction, not the reduction.
   [extract_type]'s [Const]/[TypeScheme] case only tries [whd_all] when
   [Table.is_promoted_type_var] says the constant is one, and that table is
   filled by [extract_really_ind].  Before the class has been extracted it
   answers [false] and the occurrence is kept abstract; after, it reduces.  The
   two occurrences here straddle that write:

     PROBEY ...ptr args=1 promoted=false        (kept abstract)
     PROBEX ...ptr args=1 reduced=(iptr * prov)

   One Rocq type, two ML types, in one extraction.  Neither is malformed on its
   own, so nothing downstream can object -- only the disagreement between them
   is wrong, and a disagreement has no single site to be reported at.

   An earlier reading of this file said the cause was [is_stuck] rejecting a
   [Case], and that the pattern was "always the innermost arrow."  Both were
   wrong, and wrong in the same way: they were built from counts of which
   parameters resolved at arity one and arity three, and an instrument that
   reports position cannot distinguish a positional mechanism from a temporal
   one.  [is_stuck] is never consulted for the failing occurrence.

   The ordering was nearly missed a second time.  The first read of the probe
   was [grep PROBE | sort | uniq -c], which shows both answers present and
   reads as two contexts; [sort] destroys the one property that was the whole
   finding.

   Fixed by extracting the class before asking, which makes the answer
   independent of the order uses are met in.  Which class to extract, the
   projection's own type says: it takes the record it projects from as its
   first argument.  The recursion guard is needed because extracting the class
   can reach the projection again before the memo that would stop it is
   written. *)

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
