(** A [let]-bound inner [fix] that calls the {e enclosing} [Fixpoint] cannot be
    lifted to a top-level helper --- the call would have nothing to name --- so
    it stays inline as a lambda.  Its type is therefore written by a different
    path from the lifted one's, and this pins that path down: every occurrence
    of the enclosing class instance must still be spelled through to its field,
    [typename _tcI0::IPTR::iptr] and not the instance [typename _tcI0::IPTR].

    Written as a candidate reduction of Vellvm h:40291 and {e it does not
    reproduce it} --- the inline path is correct here.  Kept as the guard that
    says so, because it is the immediate neighbour of
    [tests/regression/lifted_inner_fix_drops_class_param]: the two differ only
    in whether the inner [fix] mentions the enclosing [Fixpoint], that one
    choice decides lifted against inline, and only the lifted side was ever
    broken.  Whatever h:40291 turns out to be, it is not this. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class IPtr := { iptr : Type; zero_iptr : iptr }.
Class Ptr := { ptr : Type; zero_ptr : ptr }.

(** Both fields are themselves instances, as [Params] is in Vellvm. *)
Class Params := { PTR :: Ptr; IPTR :: IPtr }.

Section S.
  Context {Pa : Params}.

  Definition dv := (ptr * iptr)%type.

  (** The monad the inner [fix] returns into, a plain inductive as Vellvm's
      [EOU] is --- the class-typed part of the return type is [dv], not the
      carrier. *)
  Definition EOU (A : Type) := option A.

  Definition eou_ret {A : Type} (a : A) : EOU A := Some a.

  Fixpoint collect (n : nat) (xs : list dv) : EOU dv :=
    (* Unannotated, exactly as Vellvm leaves it: the return type [EOU (list dv)]
       is inferred, and that is what Crane has to write on the lambda. *)
    let go_all (pad : option nat) :=
      fix go (m : nat) (ys : list dv) : _ :=
        match ys with
        | nil => eou_ret (@nil dv)
        | cons y ys' =>
          (* The call to the enclosing [Fixpoint].  This is what keeps [go]
             inline: a lifted top-level helper could not name [collect]'s
             recursive occurrence. *)
          match collect m ys' with
          | Some z =>
            match go m ys' with
            | Some rest => eou_ret (cons z rest)
            | None => if pad then None else None
            end
          | None => None
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

Module InlineInnerFixWritesInstance.
  Definition use `{Pa : Params} (x : dv) : EOU dv := collect 0 (cons x nil).
End InlineInnerFixWritesInstance.
Crane Extraction "inline_inner_fix_writes_instance" InlineInnerFixWritesInstance.
