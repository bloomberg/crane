(** Crane bug: a *file* whose name matches a type declared in it, compared
    case-insensitively, collides with that type in the generated C++, and the
    module wins.

    ExtLib's [Structures/Monad.v] declares the class [Monad].  Crane emits a
    struct (namespace-like) [Monad] for the file and a concept [Monad] for the
    class, in the same scope.

    Expected: one of the two is renamed.
    Actual:   error: redefinition of 'Monad' as different kind of symbol
              error: 'Monad' is not a class, namespace, or enumeration

    [Crane Extraction Blacklist Monad] works around it by renaming the module.
    This test also shows the instance-qualification bug of
    [monad_instance_missing] ("no member named 'opt_monad'"), which is why that
    one blacklists [Monad] to isolate it.

    Seen in Vellvm on five names at once -- [CFG], [Compare], [Functor], [EOU],
    [Monad].  Two of the symptoms are worse than a redefinition error: the
    record [cfg] in [Syntax/CFG.v] came out with no name at all, and everything
    in [Semantics/Operations/Compare.v] was emitted *inside* the stdlib
    [Compare] inductive's struct, which dragged it thousands of lines ahead of
    every definition it refers to. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.

Import MonadNotation.
Open Scope monad.

Variant opt (X : Type) : Type := none | some (x : X).
Arguments none {X}.
Arguments some {X}.

#[global] Instance opt_monad : Monad opt :=
  {| ret _ x := some x ;
     bind _ _ c k := match c with none => none | some x => k x end
  |}.

Definition double (n : nat) : opt nat := ret (n + n).

Module ModuleTypeNameCollision.

  Definition use (n : nat) : opt nat :=
    x <- double n ;; ret (S x).

End ModuleTypeNameCollision.

Crane Extraction "module_type_name_collision" ModuleTypeNameCollision.
