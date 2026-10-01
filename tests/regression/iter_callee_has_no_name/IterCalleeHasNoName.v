(* [ITree.iter] goes through the [MonadIter] class, whose itree instance
   [MonadIter_itree] has no spelling in the reified mode -- there is no
   [Crane Extract] mapping for it in theories/Monads/ITreeReified.v.  In callee
   position that leaves the call with its template argument list intact and
   nothing in front of it, so the C++ does not parse at all.

   Expected: a named callee, e.g. [itree_iter<FailE, Nat, Nat>(...)] backed by
             a helper in crane_itree.h, the way [bind]/[ret]/[trigger] are.
   Actual:
       return <FailE, Nat, Nat>(
              ^ no callee
     error: expected expression
     error: expected '(' for function-style cast or type construction
     error: expected ';'
   and clang then resynchronises badly across the rest of the file.

   In Vellvm this regressed the build from 155 to 250 errors at Crane
   8c5f688b1.  There are 8 [return <...>] sites in the generated header --
   vellvm_bench.h:12013 ([Recursion::interp_mrec], whose ITree source at
   ITree/Interp/Recursion.v:69 is literally [fun R => ITree.iter (...)]),
   :14614, :16227, :16250 ([Intrinsics::interp_intrinsics_h]), :18670,
   :18810 ([Denotation::run_exc]), :19319, :19401.  Between them they account
   for 114 parse errors (expected '(' 47, expected ';' 34, expected
   expression 33) plus 16 "'X' does not refer to a value".

   Note the enclosing definition need NOT be generic over the monad: this
   reduction fixes the event family to [FailE] and still reproduces. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From Stdlib Require Import List.
Import ListNotations.

Variant FailE : Type -> Type := Throw : unit -> FailE void.

Module IterCalleeHasNoName.
  Definition countdown (n : nat) : itree FailE nat :=
    ITree.iter (fun k => match k with
                         | O => Ret (inr 0)
                         | S k' => Ret (inl k')
                         end) n.
End IterCalleeHasNoName.

Crane Extraction "iter_callee_has_no_name" IterCalleeHasNoName.
