(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared ITree library erasure directives.

   Imports the real InteractionTrees library and provides extraction
   Skip/Inline directives for the library infrastructure that must be
   erased regardless of extraction mode (erased vs reified).

   Both [ITree.v] (erased mode) and [ITreeReified.v] (reified mode)
   re-export this module and add their mode-specific directives.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require Import List.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps.
From ITree Require Export
     Core.ITreeDefinition
     Core.Subevent
     Indexed.Sum
     Indexed.Function
     Interp.Interp
     Interp.Handler.

Export ITreeNotations.
Open Scope itree_scope.
Import ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(* A sum of event families is a real type: a handler over [E +' F] matches on
   which side the event came from, and the answer is not in the type.  The
   index the families are applied at is erased, so the two parameters are the
   event structs themselves, and the third, the index, is left to its
   default. *)
#[export] Instance sum1_mapping (E1 E2 : Type -> Type) (X : Type) : TypeMapping (sum1 E1 E2 X) :=
  {| type_headers := ["crane_itree.h"];
     type_cpp :=
       Crane.Cpp.Apply "Sum1"
         [Crane.Cpp.TypeArg (Crane.Cpp.SourceType E1); Crane.Cpp.TypeArg (Crane.Cpp.SourceType E2)];
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (sum1 E1 E2 X);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@inl1 E1 E2 X);
             ctor_build := Expr "sum1_inl(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "std::holds_alternative<typename Sum1<%t0, %t1>::Inl1>(%scrut.v())";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "std::get<typename Sum1<%t0, %t1>::Inl1>(%scrut.v()).a0")] |} |};
          {| ctor_source := Ref (@inr1 E1 E2 X);
             ctor_build := Expr "sum1_inr(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "std::holds_alternative<typename Sum1<%t0, %t1>::Inr1>(%scrut.v())";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "std::get<typename Sum1<%t0, %t1>::Inr1>(%scrut.v()).a0")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
Crane Extract Skip void1.
Crane Extract Skip elim_void1.
Crane Extract Skip case_sum1.

#[export] Instance subevent_mapping : OperationMapping (Ref (@subevent)) := pass_through [] "e" [].

Crane Extract Skip Embeddable.
#[export] Instance embed_mapping : OperationMapping (Ref (@embed)) := pass_through [] "u" [].
Crane Extract Skip Embeddable_itree.
Crane Extract Skip Embeddable_forall.

Crane Extract Skip ITree.map.
(* [iter] is not skipped: it is reached through [MonadIter], whose instance for
   trees the mode skips, so a skipped [iter] leaves a call with no callee at
   all -- [return <E, I, R>(...)].  The helper builds the same [Tau]-guarded
   tree the Rocq definition denotes. *)
#[export] Instance iter_mapping : OperationMapping (Ref (@ITree.iter)) :=
  effect_cpp ["crane_itree.h"] ["step"; "i"] (Structured (Call "itree_iter" [] [Arg "step"; Arg "i"])).
Crane Extract Skip ITree.forever.
Crane Extract Skip ITree.spin.
Crane Extract Skip ITree.ignore.
Crane Extract Skip ITree.cat.
Crane Extract Skip translateF.

#[export] Instance Functor_itree_mapping : OperationMapping (Ref (@Functor_itree)) :=
  dictionary ["crane_itree.h"] [] "Functor_itree<%t0>".
Crane Extract Skip Applicative_itree.
(* Not skipped, unlike its siblings: a tree's [bind] and [ret] are named by
   their own mappings wherever they are written directly, but a generic
   definition constrained by [Monad] has a dictionary parameter that must be
   given a type -- [Monad_stateT<Monad_itree, S>].  The header supplies one. *)
#[export] Instance Monad_itree_mapping : OperationMapping (Ref (@Monad_itree)) :=
  dictionary ["crane_itree.h"] [] "Monad_itree<%t0>".
(* Not skipped, for the reason [Monad_itree] is not: a definition that
   iterates generically has a [MonadIter] dictionary parameter, and skipped
   the instance left the argument with no value at all. *)
#[export] Instance MonadIter_itree_mapping : OperationMapping (Ref (@MonadIter_itree)) :=
  dictionary ["crane_itree.h"] ["step"; "init"] "MonadIter_itree<%t0>".
#[export] Instance idM_mapping : OperationMapping (Ref (@idM)) := pass_through [] "e" [].

Crane Extract Skip Cat.
Crane Extract Skip Id_.
Crane Extract Skip Inl.
Crane Extract Skip Inr.
Crane Extract Skip Case.
Crane Extract Skip ReSum.
Crane Extract Skip Eq2.
Crane Extract Skip Initial.

Crane Extract Skip cat.
#[export] Instance id_mapping : OperationMapping (Ref (@id_)) := pass_through [] "a" [].
#[export] Instance inl_mapping : OperationMapping (Ref (@inl_)) := pass_through [] "bif" ["a"; "b"].
#[export] Instance inr_mapping : OperationMapping (Ref (@inr_)) := pass_through [] "bif" ["a"; "b"].
(* [case_ f g] reads which side of a sum an event came from.  Skipped, it left
   a call with no callee at all; and it cannot be spelled as a dispatch
   written out here, because the same constant is written both bare -- as the
   handler an [interp] is given -- and applied to an event.  The helper is a
   value, so it is both: what the template does not name, the use site
   applies it to.  Its value arguments are the declaration's: the bifunctor
   and the three objects come first, erased at a category over families but
   passed all the same, so the two handlers are the fifth and sixth. *)
#[export] Instance case_mapping : OperationMapping (Ref (@case_)) :=
  {| operation_headers := ["crane_itree.h"];
     operation_cpp := Structured (Call "itree_case" [] [Arg "f"; Arg "g"]);
     operation_contract :=
       PureOperation (uses Ignore ["bif"; "a"; "b"; "c"] ++ uses ReadCanonical ["f"; "g"]) ReturnValue [] |}.
#[export] Instance resum_mapping : OperationMapping (Ref (@resum)) := pass_through [] "a" ["b"].

#[export] Instance ReSum_id_mapping : OperationMapping (Ref (@ReSum_id)) := pass_through [] "a" [].
#[export] Instance ReSum_inl_mapping : OperationMapping (Ref (@ReSum_inl)) := pass_through [] "bif" ["a"; "b"; "c"].
#[export] Instance ReSum_inr_mapping : OperationMapping (Ref (@ReSum_inr)) := pass_through [] "bif" ["a"; "b"; "c"].
#[export] Instance ReSum_sum_mapping : OperationMapping (Ref (@ReSum_sum)) := pass_through [] "bif" ["a"; "b"; "c"].
Crane Extract Skip ReSum_empty.

Crane Extract Skip IFun.
Crane Extract Skip apply_IFun.
Crane Extract Skip apply_IFun'.
Crane Extract Skip as_IFun.
Crane Extract Skip Eq2_IFun.
Crane Extract Skip Id_IFun.
Crane Extract Skip Cat_IFun.
Crane Extract Skip Initial_void1.
Crane Extract Skip Case_sum1.
Crane Extract Skip Case_sum1_Handler.
Crane Extract Skip Inl_sum1.
Crane Extract Skip Inr_sum1.

Crane Extract Skip subevent_void1.

Crane Extract Skip ITree.subst.
Crane Extract Skip Module ITree.
