(* A [let] whose right-hand side is a [match] is lowered to a declaration plus
   an if/else that assigns into it, so the declaration is a name the
   right-hand side never had in Rocq.  A branch binder of the same name must
   therefore be freshened against it:

     Nat x;
     if (o.has_value()) { const Nat &x0 = *o; x = x0; }
     else               { x = Nat::s(...); }

   [MLletin] generates its right-hand side with the pre-push environment,
   which is right for the de Bruijn list -- the right-hand side is not under
   the binder, and shifting it would misread every index in it -- but wrong
   for the avoid set, which is what names are freshened against.  The two come
   apart, so the right-hand side takes the names from before the push and the
   avoid set from after.

   [three] is the same shape one level further in: the parameter is also
   called [x], so the declaration is already renamed to [x0], and it is that
   synthesised name the branch binder has to avoid.  It is the case that
   distinguishes "the parameter is in scope" from "the temporary is in scope",
   and only the second was ever in question.

   Vellvm: rocq/Semantics/Implementations/Memory.v:164, [handle_memoryM]'s
   [Alloca] branch --

     | Alloca t n align =>
         let align := match align with None => 8%N | Some align => align end in

   which emitted [align1 = align1] at vellvm_bench.h:16767. *)


From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module LetShadowsMatchBinder.

  (* Two levels: the let binder and the branch binder share a name. *)
  Definition two (o : option nat) : nat :=
    let x := match o with None => 8 | Some x => x end in S x.

  (* Three levels, as Vellvm has it: a parameter, a let over it, and a branch
     binder inside the let, all called [x]. *)
  Definition three (x : option nat) : nat :=
    let x := match x with None => 8 | Some x => x end in S x.

End LetShadowsMatchBinder.

Crane Extraction "let_shadows_match_binder" LetShadowsMatchBinder.
