(* The instance is one declaration AWAY from the body that needs it, and the
   mention that needs it is an itree bind's continuation binder:

     Definition runM : itree FailE (sum nat dval) := ...   (* at ParamsV natIPtr *)
     Definition check : itree FailE nat :=
       r <- runM ;; Ret (match r with inl e => e | inr dv => ... end).

   [check]'s body names [runM] and applies no instance at all, so nothing the
   body says resolves anything.  [runM]'s own declaration spells both promoted
   variables correctly, on the line above.  The continuation binder's type is
   re-spelled from the Rocq type of [r] rather than taken from what the call it
   binds returns:

     [](const Sum<Nat, Dval<ptr, iptr>>& r) { ... }

   against a [runM] whose signature says [Dval<typename
   ParamsV<natIPtr>::PTR::ptr, typename ParamsV<natIPtr>::IPTR::iptr>].

   Fixed: the resolution was there all along -- [runM]'s own declaration
   supplies it, and [with_body_resolutions] reads the globals the body names.
   What erased [iptr] was a second, wrong answer for it: a class field is an
   instance of its own class ([@IPTR P] is an [IPtr]), so it is recorded as
   one, and [class_arg_type] spelled the record it is selected from as a
   template argument -- [IPTR<ParamsV<natIPtr>>].  Two answers for one name
   are dropped, so the wrong one took the right one with it.  A projection
   applied to one argument is now [Tqualified].

   The import list is not harness configuration -- it selects the emission
   path. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Class IPtr := { iptr : Type ; zero_iptr : iptr ; to_Z : iptr -> nat }.
Class Provenance := { prov : Type ; nil_prov : prov }.
Class Pointer (P : Provenance) := { ptr : Type ; null : ptr }.
Class Params := { ADDR : Type ; zero_addr : ADDR
  ; PROV : Provenance ; PTR : @Pointer PROV ; IPTR : IPtr }.

Section withParams.
  Context {P : Params}.
  Variant dval : Type := | DPtr (p : @ptr PROV PTR) | DIptr (i : @iptr IPTR).

  Definition runS : itree FailE (sum nat dval) :=
    Ret (inr (DIptr (@zero_iptr IPTR))).

  Definition to_nat (d : dval) : nat :=
    match d with DPtr _ => 0 | DIptr i => @to_Z IPTR i end.
End withParams.

#[global] Instance natIPtr : IPtr := {| iptr := nat ; zero_iptr := 0 ; to_Z := fun n => n |}.
#[global] Instance ProvenanceV : Provenance := {| prov := bool ; nil_prov := false |}.
#[global] Instance PointerV : @Pointer ProvenanceV := {| ptr := (nat * bool)%type ; null := (0, false) |}.
#[global] Instance ParamsV {IP : IPtr} : Params :=
  {| ADDR := nat ; zero_addr := 0 ; PROV := ProvenanceV ; PTR := PointerV ; IPTR := IP |}.

Module ItreeBindBinderAtNamedDecl.
  (* The only declaration that names the instance. *)
  Definition runM : itree FailE (sum nat (@dval (@ParamsV natIPtr))) :=
    @runS (@ParamsV natIPtr).

  Definition to_natM (d : @dval (@ParamsV natIPtr)) : nat :=
    @to_nat (@ParamsV natIPtr) d.

  (* Names [runM] and [to_natM]; applies no instance. *)
  Definition check : itree FailE nat :=
    ITree.bind runM (fun r => Ret (match r with inl e => e | inr dv => to_natM dv end)).
End ItreeBindBinderAtNamedDecl.

Set Crane Format Style "None".
Crane Extraction "itree_bind_binder_at_named_decl" ItreeBindBinderAtNamedDecl.
