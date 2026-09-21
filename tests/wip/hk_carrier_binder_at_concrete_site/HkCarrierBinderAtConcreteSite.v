(** A holder struct is emitted with its *binder* rather than the concrete
    carrier, at a use site that has no binder in scope.

    Crane 486862356 mints `_crane_carrier_tchN` for a carrier of arity above
    one and writes `NAME<T1>::template c`.  Inside the traversal instances that
    is right -- `TFunctor_mcfg` is a template and `T1` is its parameter, and
    those three sites now compile.  But Vellvm also instantiates the same
    traversal from a *non-generic* definition:

        Class ConvertTyp (F: Set -> Set) := convert_typ : list (ident*typ) -> F typ -> F dtyp.
        Instance ConvertTyp_mcfg : ConvertTyp mcfg := fun env => tfmap (typ_to_dtyp env).

    with `mcfg = fun T => modul T (cfg T)`.  That emits

        static inline const ConvertTyp<mcfg> ConvertTyp_mcfg = []() {
          ...
          return Traversal::template tfmap<_crane_carrier_tch1<T1>::template c>([]() {

    and there is no `T1` here -- this is a `static inline const` initialiser, not
    a template.  The concrete carrier is known (`cfg`), and the working sites in
    the same header show the spelling that wants emitting:
    `_crane_carrier_tch1<cfg>::template c`.

    Two diagnostics, one defect.  The second is knock-on: with `T1` undeclared
    clang cannot see `_crane_carrier_tch1<T1>` as a template, so it also rejects
    the `template` keyword.

        error: use of undeclared identifier 'T1'
        error: 'template' keyword not permitted here

    Expected: `convert_holder` names `cfg`, or whatever the concrete argument is.
*)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.
#[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

Record box (T : Set) : Set := mk_box { b_payload : T }.
#[global] Instance TFunctor_box : TFunctor box | 50 :=
  fun U V f b => mk_box _ (f (b_payload _ b)).

(* arity two, like Vellvm's [modul T FnBody] *)
Record holder (T : Set) (Body : Set) : Set :=
  mk_holder { h_head : T ; h_body : Body }.

#[global] Instance TFunctor_holder {FnBody : Set -> Set} `{TFunctor FnBody}
  : TFunctor (fun T => holder T (FnBody T)) | 50 :=
  fun U V f m => mk_holder _ _ (f (h_head _ _ m)) (tfmap f (h_body _ _ m)).

(* [hbox = fun T => holder T (box T)], the concrete arity-two carrier. *)
Class Convert (F : Set -> Set) : Type := convert : nat -> F nat -> F bool.

(* non-generic: no binder is in scope at this use of [tfmap]. *)
#[global] Instance Convert_holder : Convert (fun T => holder T (box T)) :=
  fun n => tfmap (fun x => Nat.ltb n x).

Definition run (m : holder nat (box nat)) : holder bool (box bool) := convert 3 m.

Crane Extraction "hk_carrier_binder_at_concrete_site" run.
