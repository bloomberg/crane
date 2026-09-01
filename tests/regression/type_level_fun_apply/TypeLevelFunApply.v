(** A type-level function ([sem : ty -> Type]) erases to [std::any].  A value of
    that type is applied with a direct call rather than through the tolerant
    [crane_call_erased] helper:

    {v
      type 'TypeLevelFunApply::sem' (aka 'std::any') does not provide a call operator
    v} *)

Require Crane.Extraction.

Module TypeLevelFunApply.

Inductive ty := TNat | TArr : ty -> ty -> ty.

Fixpoint sem (t : ty) : Type :=
  match t with TNat => nat | TArr a b => sem a -> sem b end.

Definition app (a b : ty) (f : sem (TArr a b)) (x : sem a) : sem b := f x.

Definition test : nat := app TNat TNat (fun n : nat => n) 3.

End TypeLevelFunApply.

Crane Extraction "type_level_fun_apply" TypeLevelFunApply.
