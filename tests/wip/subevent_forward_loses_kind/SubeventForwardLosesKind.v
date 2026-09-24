(* A family parameter that is never applied in its own declaration, but is
   handed to a constructor that expects a template name, comes out kinded
   `typename`.

     template <typename T1 = void, typename T2>
     std::vector<T2> raiseUB(Sub<UBE, T1> s);

   `Sub` is emitted higher-kinded --

     template <template <typename> class f, template <typename> class g>
     using Sub = std::function<g<std::any>(f<std::any>)>;

   -- so the declaration cannot type-check against its own parameter's type:
   `template argument for template template parameter must be a class
   template`.  The kind is read from *direct application* of the variable
   (`Gen_decls.applied_tvar_arities`, `Ml_type_util.higher_kinded_ml_tvars`),
   and an occurrence as an argument at another constructor's higher-kinded
   position does not count -- even though the position's kind is recorded, in
   `Table.add_hkt_ind_params`, by the very pass that emitted `Sub`.

   Adding one parameter that does apply `E` is the whole difference: give
   `raiseUB` an `(e : E nat)` and the head comes out
   `template <template <typename> class T1, typename T2>` and compiles.

   Reduced by the Vellvm session from LLVMEvents.raiseUB, where
   `raiseUB {E} `{UBE -< E} {X} : itree E X` has `E` in exactly two places:
   the subevent class, and the result type.  `itree E X` extracts to
   `ITree<X>`, dropping the event parameter, so the class argument is the only
   occurrence left -- and it is an argument, not an application.  Four sites
   there (`raiseLLVM`, `raiseUB`, `raise`, `raiseOOM`) behind 24 of 31 errors.

   This is the caller half.  The callee half -- `trigger_cast`'s own family
   parameter collapsing to a plain parameter -- is a separate defect and is
   not reproduced here. *)

From Crane Require Import Extraction.
Require Import List.

Inductive UBE (A : Type) : Type := throwub : unit -> UBE A.
Arguments throwub {A}.

(* The shape of `UBE -< E`: a class projection, and the only place the
   caller's own family parameter is applied. *)
Class Sub (F G : Type -> Type) := inj : forall X, F X -> G X.

Definition trigger_cast (E : Type -> Type) (B : Type) (e : E nat) : list B :=
  nil.

Module SubeventForwardLosesKind.
  (* [E] is applied nowhere in this declaration -- it survives only inside the
     projection's type. *)
  Definition raiseUB (E : Type -> Type) (S : Sub UBE E) (B : Type) : list B :=
    trigger_cast E B (inj nat (throwub tt)).

  Instance sub_refl : Sub UBE UBE := fun X e => e.

  Definition run : nat := length (raiseUB UBE sub_refl nat).
End SubeventForwardLosesKind.

Crane Extraction "subevent_forward_loses_kind" SubeventForwardLosesKind.
