(* A class constraint whose carrier is a lambda over a two-parameter
   constructor is printed as the bare constructor, and the declaration it
   appears in is ill-formed.

   Rocq writes

     `{TFunctor (fun T => two T (FnBody T))}

   and Crane prints the constraint as [TFunctor<two>].  [two] takes two
   parameters where the class wants one, so the *declaration* does not
   compile --

     error: too few template arguments for class template 'two'

   -- and every call to the enclosing function then reports "no matching
   function" with no viable candidate, because there is no candidate.  The
   carrier written at the call site is irrelevant here: this is upstream of
   the call, and it will persist under a correct carrier.

   The abstraction is what got dropped.  The C++ the constraint wants is an
   alias template --

     template <typename T> using c = two<T, F<T>>;

   -- the same device the printer already mints for a composite [Ttyctor]
   ({!Minicpp.abstract_cpp_type}'s sentinel).  What is missing is that the
   constraint position reaches the printer as a head rather than as a body to
   abstract.

   Note the contrast with [hk_call_carrier_erased]'s [TFunctor_outer]: there
   the two-parameter constructor is the instance's *own* carrier, which is
   handled; here it is the carrier of a constraint the instance is abstracted
   over.

   Vellvm: rocq/Syntax/Traversal.v:883, [TFunctor_mcfg], whose constraint is
   [`{TFunctor (fun T => definition T (FnBody T))}].  This is what gates
   [TFunctor_mcfg] even though 0f0d8890e writes its call-site carrier
   correctly as [TFunctor_mcfg<cfg>], and the [tfmap] inside its lambda is
   downstream of the same defect -- 3 of the 22 remaining errors are this one
   at three depths. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

#[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

(* Two parameters, as Vellvm's [definition T FnBody] has. *)
Record two (T : Set) (Body : Set) : Set := mk_two { t_head : T ; t_body : Body }.

#[global] Instance TFunctor_two {FnBody : Set -> Set} `{TFunctor FnBody}
  : TFunctor (fun T => two T (FnBody T)) | 50 :=
  fun U V f p => mk_two _ _ (f (t_head _ _ p)) (tfmap f (t_body _ _ p)).

Record outer1 (T : Set) (Body : Set) : Set := mk_outer1 { o_inner : Body }.

(* The constraint, not the head, is the defect: [`{TFunctor (fun T => two T
   (FnBody T))}] is a class applied to a lambda over a two-parameter record. *)
#[global] Instance TFunctor_outer1 {FnBody : Set -> Set}
       `{TFunctor FnBody}
       `{TFunctor (fun T => two T (FnBody T))}
  : TFunctor (fun T => outer1 T (two T (FnBody T))) | 50 :=
  fun U V f m => mk_outer1 _ _ (tfmap f (o_inner _ _ m)).

Module HkConstraintCarrierTwoParams.

  Definition run (m : outer1 nat (two nat (list nat)))
    : outer1 nat (two nat (list nat)) := tfmap S m.

End HkConstraintCarrierTwoParams.

Crane Extraction "hk_constraint_carrier_two_params" HkConstraintCarrierTwoParams.
