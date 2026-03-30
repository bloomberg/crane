(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63 Sint63Axioms PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Open Scope int63.

Axiom Conc : forall {z : int}, Type -> Type.
Axiom Cret : forall {A}, A -> @Conc 0 A.
Axiom Cbind : forall {x y A B}, @Conc x A -> (A -> @Conc y B)-> @Conc (add x y) B.
Axiom Ceval : forall {A}, @Conc 0 A -> A.

Axiom thread : Type.
Axiom mk_thread  : forall {A B}, (A -> B) -> A -> @Conc 1 thread.
Axiom join : thread -> @Conc (PrimInt63.sub 0 1) unit.
Axiom sleep : int -> @Conc 0 unit.
Axiom print_endline : string -> @Conc 0 unit.

Crane Extract Monad Conc [ bind := Cbind , ret := Cret ].
Crane Extract Inlined Constant Ceval => "%a0".
Crane Extract Inlined Constant thread => "std::thread" From "thread".
Crane Extract Inlined Constant mk_thread => "std::thread(%a0, %a1)".
Crane Extract Inlined Constant join => "%a0.join()".
Crane Extract Inlined Constant sleep => "std::this_thread::sleep_for(std::chrono::milliseconds(%a0))" From "thread" "chrono".
Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'".

Module ConcNotations.

  Declare Scope Concmonad_scope.
  Delimit Scope Concmonad_scope with Concmonad.
  Open Scope Concmonad.

  Notation "e1 ;; e2" := (@Cbind _ _ _ _ e1%Concmonad (fun _ => e2%Concmonad))
    (at level 61, right associativity) : Concmonad_scope.
  Notation "x <- c1 ;; c2" := (@Cbind _ _ _ _ c1%Concmonad (fun x => c2%Concmonad))
    (at level 61, c1 at next level, right associativity) : Concmonad_scope.

End ConcNotations.

Import ConcNotations.
