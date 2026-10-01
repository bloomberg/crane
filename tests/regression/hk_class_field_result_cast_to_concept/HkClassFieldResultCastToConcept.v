(** An expression whose type is an application of a higher-kinded class field
    is cast to the {e concept}, which is not a type.

    {v
      template <MMP _tcI0> memM<typename _tcI0::PROV::provenance> allocate() {
        return mbind<_tcI0, typename _tcI0::mm_state::state,
                     typename _tcI0::PROV::provenance>(
            std::any_cast<MMP>(_tcI0::get_state()),
            ...
              std::any_cast<MMP>(_tcI0::mk_prov(_tcI0::fresh_ptr(s))));
    v}

    {v
      error: no matching function for call to 'any_cast'
    v}

    The cast node holds [Tglob (MMP, [], [])] --- the class reference itself,
    at no arguments, used as a type.  Probed at the printer, so that is what
    the AST says and not an inference from the text.

    Both casts sit where the expected type is an application of [memM], the
    class's [Type -> Type] field: [memM state] at the first, and the domain of
    a [mret] instantiated at [memM provenance] at the second.  Every {e other}
    position in the same function resolves correctly ---
    [typename _tcI0::PROV::provenance], [typename _tcI0::mm_state::state] ---
    so the resolution machinery is working and this is not a missing
    resolution.  Something upstream of the cast records the class where it
    should record the field application.

    {b What this file was written for, and does not show.}  It was built to
    reduce the Vellvm session's unified §174/§192 account: that an associated
    type erases exactly when its spelling is a free name at the point of
    printing, so a concept and an instance struct erase {e complementary}
    arguments of the same application.  At this size the concept is spelled
    correctly throughout --- [typename I::PTR::ptr],
    [typename I::mm_state::state] --- and no complementary erasure appears.
    The three file-scope [using ptr = std::any;] aliases are emitted, but
    nothing in this file resolves to them.

    So the §174 shape needs something this reduction does not have, and the
    account is neither confirmed nor refuted here.  What the file does hold is
    the defect above, which is real, small, and separate. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class PtrC := { ptr : Type ; nullp : ptr }.
Class ProvC := { provenance : Type ; noprov : provenance }.
Class StateC := { state : Type ; init : state }.

Class MMP := {
  PTR : PtrC ;
  PROV : ProvC ;
  mm_state : StateC ;
  memM : Type -> Type ;
  mret : forall A, A -> memM A ;
  mbind : forall A B, memM A -> (A -> memM B) -> memM B ;
  get_state : memM (@state mm_state) ;
  mk_prov : @ptr PTR -> @provenance PROV ;
  fresh_ptr : @state mm_state -> @ptr PTR ;
}.

Section M.
  Context {MM : MMP}.

  Definition allocate : memM (@provenance PROV) :=
    mbind _ _ get_state (fun s => mret _ (mk_prov (fresh_ptr s))).
End M.

#[global] Instance natPtr : PtrC := {| ptr := nat ; nullp := 0 |}.
#[global] Instance natProv : ProvC := {| provenance := nat ; noprov := 0 |}.
#[global] Instance natState : StateC := {| state := nat ; init := 0 |}.

#[global] Instance natMMP : MMP := {|
  PTR := natPtr ; PROV := natProv ; mm_state := natState ;
  memM := fun A => A ;
  mret := fun _ a => a ;
  mbind := fun _ _ m k => k m ;
  get_state := 7 ;
  mk_prov := fun p => S p ;
  fresh_ptr := fun s => s ;
|}.

Module HkClassFieldResultCastToConcept.
  Definition run : nat := @allocate natMMP.
End HkClassFieldResultCastToConcept.
Crane Extraction "hk_class_field_result_cast_to_concept" HkClassFieldResultCastToConcept.
