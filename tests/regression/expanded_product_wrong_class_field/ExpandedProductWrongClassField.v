(** One Rocq type, two spellings in one declaration: named and correct in the
    return type, expanded and {e wrong} in the parameter list.

    [fused] is an alias for a product whose first component is [state], a
    record parameterised by three fields of a class instance.  A parameter
    Rocq infers rather than reads off an annotation arrives at translation as
    the {e unfolded} product, and converting that expansion picks a different
    field of the same class for the first component -- [prov] where [state]
    belongs -- while the return type, which still names the alias, is right.

    Scope cannot be the difference: the two spellings are in one signature.

    Seen in Vellvm at [vellvm_bench.h:86467], from
    [rocq/Semantics/InterpretationStack.v:108], against the correct spelling
    twelve lines below it at [:86487].  It terminates overload resolution for
    [interp_mcfg], and with it [interpreter_gen], [interpreter_param] and
    [run_program]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Prov := {
  provenance : Type;
  allocationId : Type;
  prov : Type;
  no_prov : prov;
  a_provenance : provenance;
  an_allocationId : allocationId;
}.

Class Ptr := { ptr : Type; zero_ptr : ptr }.

(** The fields are themselves instances: the wrong spelling in Vellvm is
    [typename _tcI0::PROV::prov], a sibling field of an {e inner} class. *)
Class ParamsV := { PROV :: Prov; PTR :: Ptr }.

Section S.
  Context {Pa : ParamsV}.

  Record state := mk_state {
    st_prov : provenance;
    st_alloc : allocationId;
    st_ptr : ptr;
  }.

  Definition frame := list ptr.

  Definition fused := (state * frame)%type.

  (** Reads the expanded product, so the caller's parameter is inferred at it
      rather than at the alias. *)
  Definition top (p : state * frame) : ptr := st_ptr (fst p).

  (** [s] is unannotated: Rocq infers it from [top]'s domain.  The return type
      still names [fused]. *)
  Definition step s : fused := (fst s, snd s).

  Definition initial : fused := (mk_state a_provenance an_allocationId zero_ptr, nil).
End S.

Module ExpandedProductWrongClassField.
  Definition use `{Pa : ParamsV} : ptr := top (step initial).
End ExpandedProductWrongClassField.
Crane Extraction "expanded_product_wrong_class_field" ExpandedProductWrongClassField.
