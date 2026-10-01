(* A function returning [unit], stored where its type is erased and read back
   there.  Two defects met on the way:

   - [existT nat (touch, 3)]: the call writes [sigT]'s payload at the erased
     instantiation ([pair<obj, obj>]), but its fields were instantiated from
     the annotation ([pair<fn<void(obj)>, obj>]), so [touch] was adapted to
     [crane_erase_fn<void>] -- a box holding [fn<void(obj)>] that the
     consumer's [any_cast<fn<obj(obj)>>] cannot open.
   - [crane_erase_fn] adapting a [void] callable to an erased result returned
     an empty [crane::obj], where every consumer opens unit as
     [std::monostate].

   Expected: [check] is [true].
   Before:   [std::bad_any_cast]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module ErasedUnitResult.
  Definition touch (n : nat) : unit := tt.

  Definition packed : {T : Type & T -> unit} := existT (fun T => T -> unit) nat touch.

  Definition boxed : {T : Type & T} := existT (fun T => T) (nat -> unit) touch.

  Definition run_twice {A : Type} (f : A -> unit) (x : A) : unit :=
    match f x with tt => f x end.

  Definition is_tt (u : unit) : bool := match u with tt => true end.

  Definition through_sig (p : {T : Type & ((T -> unit) * T)%type}) : bool :=
    match p with existT _ _ (f, x) => is_tt (f x) end.

  Definition check : bool :=
    through_sig (existT (fun T => ((T -> unit) * T)%type) nat (touch, 3)).
End ErasedUnitResult.

Crane Extraction "erased_unit_result" ErasedUnitResult.
