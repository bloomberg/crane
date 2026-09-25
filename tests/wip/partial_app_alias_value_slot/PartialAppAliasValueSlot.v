(* A type alias that is a PARTIAL APPLICATION gets its value parameter in the
   wrong slot.

     Definition Top := itree TopE.            (* itree given one argument *)

   [itree : Type -> Type -> Type], so [Top : Type -> Type] and [@Top P R] is
   [itree (TopE P) R].  Crane eta-expands the alias to supply the missing value
   parameter, and the promoted parameters LEAD rather than trail (they are
   defaulted, and a defaulted parameter may not precede a plain one).  So the
   eta-added value parameter is appended LAST while the body's slot is filled
   positionally from the FRONT:

     template <typename iptr, typename r>
     using Top = std::shared_ptr<ITree<iptr>>;   // wants ITree<r>

   Each convention is right alone. Eta-expansion appends; positional
   substitution reads from the beginning. Nothing is erased, unbound or
   ambiguous -- a well-formed name in the wrong position, which is why it is
   invisible to every unbound-name instrument and why the diagnostic lands
   several calls downstream.

   The import list is not harness configuration -- it selects the emission
   path. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Class IPtr := { iptr : Type ; zero_iptr : iptr }.

Section withIPtr.
  Context {P : IPtr}.
  Variant dval : Type := | DIptr (i : @iptr P).

  (* The event family mentions the class field, so the alias is parameterised. *)
  Variant TopE : Type -> Type := Fail : dval -> TopE void.

  (* [itree] applied to ONE argument: the value parameter is missing. *)
  Definition Top := itree TopE.

  Definition seed : Top dval := Ret (DIptr (@zero_iptr P)).
End withIPtr.

#[global] Instance natIPtr : IPtr := {| iptr := nat ; zero_iptr := 0 |}.

Module PartialAppAliasValueSlot.
  Definition go : @Top natIPtr (@dval natIPtr) := @seed natIPtr.
End PartialAppAliasValueSlot.

Crane Extraction "partial_app_alias_value_slot" PartialAppAliasValueSlot.
