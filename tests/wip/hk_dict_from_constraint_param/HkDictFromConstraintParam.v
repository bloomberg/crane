(* A dictionary that arrives as a constraint *parameter* still knows its
   carrier, and the call does not write it.

   0f0d8890e reads a higher-kinded carrier off the dictionary argument, by
   descending through the adapter lambda to the instance its body names.  That
   covers a dictionary that *is* a named global instance.  It does not cover
   one that is a parameter of the enclosing function:

     ... TFunctor_holder(..., std::type_identity_t<TFunctor<box>> h0, ...) {
       ...
       return TFunctor_list_(h0, _x0, _x1);   // wants TFunctor_list_<box>
     }

   There is no instance body to descend to -- [h0] is a binder -- and
   [dict_carrier_type_args] finds nothing.  But the carrier is not lost: it is
   written in [h0]'s own declared type, which the enclosing signature already
   spells.  So this is a second source for the same query, adjacent to the one
   that landed, and the two should share their consumer rather than each
   growing their own call-site branch.

   The shape is [tfmap f (h_boxes m)] inside [TFunctor_holder]: it resolves to
   the ambient [`{TFunctor box}], not to a global instance, because the
   instance is being *abstracted over*.

   Vellvm: [TFunctor_modul] at rocq/Syntax/Traversal.v:859, the
   [tfmap f (m_globals m)] and [tfmap f (m_declarations m)] lines, which resolve
   to the ambient [`{TFunctor global}] and [`{TFunctor declaration}].  2 of the
   22 remaining errors. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

#[global] Instance TFunctor_list : TFunctor list | 50 := List.map.
#[global] Instance TFunctor_list' {F} `{TFunctor F}
  : TFunctor (fun T => list (F T)) | 49 := fun U V f => List.map (tfmap f).

Record box (T : Set) : Set := mk_box { b_payload : T }.
#[global] Instance TFunctor_box : TFunctor box | 50 :=
  fun U V f b => mk_box _ (f (b_payload _ b)).

Record holder (T : Set) (Body : Set) : Set :=
  mk_holder { h_boxes : list (box T) ; h_body : Body }.

(* [`{TFunctor box}] is what makes the dictionary a parameter: the inner
   [tfmap] below resolves to it rather than to [TFunctor_box] itself. *)
#[global] Instance TFunctor_holder {FnBody : Set -> Set}
       `{TFunctor FnBody}
       `{TFunctor box}
  : TFunctor (fun T => holder T (FnBody T)) | 50 :=
  fun U V f m => mk_holder _ _ (tfmap f (h_boxes _ _ m)) (tfmap f (h_body _ _ m)).

Module HkDictFromConstraintParam.

  Definition run (m : holder nat (list nat)) : holder nat (list nat) := tfmap S m.

End HkDictFromConstraintParam.

Crane Extraction "hk_dict_from_constraint_param" HkDictFromConstraintParam.
