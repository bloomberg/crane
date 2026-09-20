(* Expected: compiles.
   Actual:   error: use of undeclared identifier 'T2'

   A class over a higher-kinded index, instantiated at [fun T => option (F T)].
   The emitted body of the [option] instance casts with an index nobody
   declared:

     std::optional<T1<std::any>> Traversal::TFunctor_option(
         TFunctor<T1> h, F1&& f, const std::optional<T1<std::any>>& ot){
       ... std::any_cast<T1<T2>>(t0) ...

   [t0] is already a [T1<std::any>] -- it is destructured from [ot], whose type
   the same signature spells [T1<std::any>] -- so [T1<std::any>] is the
   spelling that makes the cast a no-op.  [T2] is declared nowhere: the head
   declares [T1, F1] only.

   Both instances are here on purpose.  The [list] one is the control and comes
   out correct, and the difference between the two is the interesting part:

     list:    Traversal::template tfmap<T1, std::any, std::any>(h, f, _x0)
     option:  Traversal::tfmap(h, f, std::any_cast<T1<T2>>(t0))

   The [list] body keeps explicit template arguments on the recursive [tfmap]
   and erases both indices to [std::any]; the [option] body drops them and
   tries to recover the index with a cast instead.  The structural difference
   between the two Rocq definitions is that [list]'s goes through [List.map],
   so the recursive call sits under a lambda, while [option]'s is a direct
   application in a match branch.

   This file also exposes a SECOND, unrelated defect, which is why it is two
   failures rather than one.  Both [on_option] and [on_list] emit their call as

     return tfmap([]() { return [](std::function<std::any(std::any)> _x0,
                                   List<std::any> _x1) -> List<std::any> {...}; }(),
                  bump, l);

   and [tfmap]'s first parameter is [TFunctor<T1>] with
   [template <typename> class T1] -- which cannot be deduced from a lambda, so
   both calls fail with [no matching function for call to 'tfmap'].  That hits
   the correct [list] control too, so it is independent of the [T2] above and
   will need fixing before this file can go green.  Vellvm does not reach it:
   it calls [tfmap] with explicit arguments at every site.

   Vellvm: rocq/Syntax/Traversal.v:508, the last undeclared [T2] in the
   extraction (1 of 52).  The sibling [TFunctor_list'] at :504 was the other
   half of this pair and was fixed by 0b5ca4c4d. *)

From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.

Section TFunctor.

  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

  (* Control: comes out correct. *)
  #[global] Instance TFunctor_list' {F} `{TFunctor F}
    : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  (* The bug. *)
  #[global] Instance TFunctor_option {F} `{TFunctor F}
    : TFunctor (fun T => option (F T)) | 50 :=
    fun U V f ot => match ot with None => None | Some t => Some (tfmap f t) end.

End TFunctor.

Module HkInstanceBodyTargUndeclared.

  Definition bump (n : nat) : nat := S n.

  Definition on_option (o : option (list nat)) : option (list nat) :=
    tfmap bump o.

  Definition on_list (l : list (list nat)) : list (list nat) :=
    tfmap bump l.

End HkInstanceBodyTargUndeclared.

Crane Extraction "hk_instance_body_targ_undeclared" HkInstanceBodyTargUndeclared.
