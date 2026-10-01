(** One variable against [bind_continuation_binder_field_order]: the enclosing
    [Fixpoint] gains a parameter whose type is the class's {e second} [Type]
    field ([a : addr], where [Params] declares [tag] first).  Nothing else
    moves --- the field order, [dv], [DAddr], the two nested [bind]s and the
    inline [fix] are the file next door.

    {b The question it was built to answer.}  The Vellvm session's rule was
    "the filler is the class's first-declared [Type] field", derived from two
    reorder experiments.  That rule is about the expected type [mlt] at the
    lambda, not about the fill, and its positional character is inherited from
    whoever builds [mlt].  Putting the second field in the enclosing
    signature's domain separates the two candidate sources: a filler that
    stayed [tag] would mean [mlt] never reads the enclosing signature, and one
    that flipped to [addr] would mean the reorder experiments measured a
    coincidence of two files in which the first field was also the only field
    in scope.

    {b The question is void, and the file is kept for a different one.}  Both
    branches were about where a guess reads its answer, and the guess
    ([Gen_decls.rewrite_ml_ast_types]) is deleted in crane [a290bbbab]; there
    is no filler left to be positional.  What survives is the input, and it is
    a good one on its own terms: an enclosing recursive function whose {e own
    domain} mentions a class field, threaded through the inline [fix]'s
    self-calls.  That is a position [ml_app_result_type] has to instantiate
    correctly --- the recursive call [bytes_to_dv a k bs0] now carries a
    class-dependent argument --- and nothing else in the corpus exercises it.

    So: not a reduction, and not the discriminator it was built as.  A
    widening, labelled as one.

    The control is unchanged and still internal: the [bind] outside the inline
    [fix], eleven lines from the sites of interest in the same emitted
    function.

    Ported from the Vellvm session's
    [src/crane/reductions/bind_continuation_binder_mlt_domain] ([65656e00]),
    unchanged in substance. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type :=
| Ok : A -> EOU A
| Err : nat -> EOU A.

Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end
  |}.

(** Field order identical to [bind_continuation_binder_field_order]. *)
Class Params := { tag : Type ; addr : Type ; t0 : tag ; zero : addr }.

Inductive dv (P : Params) : Type :=
| DAddr : tag -> addr -> dv P
| DNum : nat -> dv P.

Arguments DAddr {P}.
Arguments DNum {P}.

Inductive byte (P : Params) : Type :=
| B : nat -> byte P.

Arguments B {P}.

(** The variable: [a : addr] in the enclosing [Fixpoint]'s domain.  In the file
    next door this parameter does not exist and the domain mentions no field of
    [Params] at all. *)
Fixpoint bytes_to_dv {P : Params} (a : addr) (n : nat) (bs : list (byte P))
  : EOU (dv P) :=
  match n, bs with
  | O, _ => ret (DNum 0)
  | S k, nil => ret (DAddr t0 a)
  | S k, cons (B v) rest =>
      let fix go (ds : list nat) (bs0 : list (byte P)) : EOU (list (dv P)) :=
          match ds with
          | nil => ret nil
          | cons _ ds' =>
              bind (bytes_to_dv a k bs0)
                   (fun (f : dv P) =>
                      bind (go ds' bs0)
                           (fun (r : list (dv P)) => ret (cons f r)))
          end
      in bind (go (cons v nil) rest) (fun r => ret (DNum (length r)))
  end.

#[global] Instance natParams : Params :=
  {| tag := bool ; addr := nat ; t0 := true ; zero := 0 |}.

Module BindContinuationBinderMltDomain.
  Definition run : EOU (dv natParams) :=
    @bytes_to_dv natParams 0 2 (cons (B 1) nil).
End BindContinuationBinderMltDomain.
Crane Extraction "bind_continuation_binder_mlt_domain" BindContinuationBinderMltDomain.
