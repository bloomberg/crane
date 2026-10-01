From Crane Require Import Mapping.Std.

(** The class whose instances are resolved implicitly. *)
Class Dec (A : Set) := { dec : A -> A -> bool }.

(** An inductive whose capitalised C++ name is [Ident].  It is declared here,
    in a file other than [AstLike], so that [AstLike]'s child module [Ident]
    collides with it.  That collision is what turns [AstLike] into a wrapper
    struct, which is the whole point of the test. *)
Inductive ident : Set := Global (n : nat) | Local (n : nat).
