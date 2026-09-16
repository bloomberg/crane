(** Crane bug: a definition whose name begins with the name of the file
    declaring it is silently dropped.

    [EOU.v] declares the type [EOU] and the instance [EOU_monad].  The module
    is renamed to [EOU0], correctly, because the file is eponymous with a type
    it declares.  But [EOU_monad] shares that same prefix, and the textual
    fallback that decides what a name is contained in reads the shared prefix
    as containment -- so the instance is emitted nowhere, while [option_ub],
    which has no shared prefix, is emitted as [EOU0::option_ub].

    Nothing is reported at extraction time; the definition just vanishes, and
    the failure surfaces only at every use site.

    Expected: [struct EOU_monad] at top level, as when the file is named
              anything else.
    Actual:   error: use of undeclared identifier 'EOU_monad'

    This is the residue of [monad_instance_missing] after d77449c8: that test
    had the instance in a file whose name shared no prefix with it, and passes
    now.  Seen in Vellvm 19 times, on exactly this [EOU_monad] in
    [Semantics/EOU.v]. *)

From Crane Require Extraction.
From ExtLib Require Import Structures.Monads.

Variant EOU {X : Type} : Type :=
  | raise_error (s : nat) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU : clear implicits.

(* The name of this instance begins with the name of the file (and of the type)
   declaring it. *)
#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
     bind _ _ c k :=
       match c with
       | raise_error s => raise_error s
       | raise_ret x => k x
       end
  |}.

Definition option_ub {X : Type} (s : nat) (x : option X) : EOU X :=
  match x with None => raise_error s | Some v => raise_ret v end.
