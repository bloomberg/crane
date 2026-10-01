(** A [let]-bound inner function inside a [Fixpoint] is lifted to a top-level
    helper, and the lift keeps the [typename _tcI0::...] spellings its body was
    written with while giving the helper a template head that does not declare
    [_tcI0]:

    {v
      template <typename T1>
      std::optional<List<dv<typename _tcI0::PTR::ptr, ...>>>
      _collect_go_all(const std::optional<Nat> pad) { ... }
    v}

    Every mention of the enclosing class instance is then an undeclared
    identifier.  Found while reducing Vellvm h:40291 --- that one keeps the
    [fix] inline and misspells its {e return type}; this is the neighbouring
    case where the same [let]-bound [fix] is lifted instead, and it is a
    distinct defect. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class IPtr := { iptr : Type; zero_iptr : iptr }.
Class Ptr := { ptr : Type; zero_ptr : ptr }.

(** Both fields are themselves instances, as [Params] is in Vellvm. *)
Class Params := { PTR :: Ptr; IPTR :: IPtr }.

Section S.
  Context {Pa : Params}.

  Definition dv := (ptr * iptr)%type.

  (** The monad the inner [fix] returns into. *)
  Definition EOU (A : Type) := option A.

  Definition eou_ret {A : Type} (a : A) : EOU A := Some a.

  (** The outer [Fixpoint] is what makes the inner one a [let]-bound [fix]
      rather than a top-level definition. *)
  Fixpoint collect (n : nat) (xs : list dv) : EOU dv :=
    (* Unannotated: the return type [EOU (list dv)] is inferred from the
       branches, and that is the type Crane has to write on the lambda. *)
    let go_all (pad : option nat) :=
      fix go (m : nat) (ys : list dv) : _ :=
        match ys with
        | nil => eou_ret (@nil dv)
        | cons y ys' =>
          match go m ys' with
          | Some rest => eou_ret (cons y rest)
          | None => if pad then None else None
          end
        end
    in
    match xs with
    | nil => None
    | cons x xs' =>
      match n with
      | O => match go_all None n xs with
             | Some (cons z _) => eou_ret z
             | _ => eou_ret x
             end
      | S n' => collect n' xs'
      end
    end.
End S.

Module LiftedInnerFixDropsClassParam.
  Definition use `{Pa : Params} (x : dv) : EOU dv := collect 0 (cons x nil).
End LiftedInnerFixDropsClassParam.
Crane Extraction "lifted_inner_fix_drops_class_param" LiftedInnerFixDropsClassParam.
