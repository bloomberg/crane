From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.

(** A memoised longest-prefix scan shaped like ParseALot's [max_pref_fn_M],
    over a list mapped to a cons list whose match template binds the tail as
    a variable of its own ([auto %b1a1 = %scrut.tail()]) and the head by
    reference.  The tail is a copy, not a part of the scrutinee: the call
    entering the machine takes it by move.  The frame saved across the call
    copies the head, a part of the list, before moving the list in after it,
    instead of copying the list. *)
Module FrameSaveCopiedBinder.

Definition accepting (st : list nat) : bool :=
  match st with
  | x :: _ => even x
  | [] => false
  end.

Definition step (a : nat) (st : list nat) : list nat := a :: st.

Definition lookup (m : option nat) (a : nat) : option (option (list nat * list nat * nat)) :=
  match m with
  | Some k => if k =? a then Some None else None
  | None => None
  end.

Fixpoint scan (m : option nat) (s : list nat) (i : nat) (st : list nat)
  : nat * option (list nat * list nat * nat) :=
  match s with
  | [] => if accepting st then (0, Some ([], [], i)) else (1, None)
  | a :: s' =>
    let st' := step a st in
    let mp :=
      match lookup m a with
      | None => scan m s' (pred i) st'
      | Some o => (2, o)
      end
    in
    match mp with
    | (c, None) =>
      if accepting st' then (c, Some ([a], s', pred i))
      else if accepting st then (c, Some ([], s, i))
      else (S c, None)
    | (c, Some (p, q, qi)) => (c, Some (a :: p, q, qi))
    end
  end.

End FrameSaveCopiedBinder.

Module ListMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance list_mapping (A : Type) : TypeMapping (list A) :=
  {| type_headers := ["conslist.h"];
     type_cpp := Crane.Cpp.Apply "crane::list" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@cons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (list A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@nil A);
             ctor_build := Expr "crane::list<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@cons A);
             ctor_build := Expr "crane::cons(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.tail()")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End ListMapping.

Set Crane Loopify.
Crane Extraction "frame_save_copied_binder" FrameSaveCopiedBinder.
