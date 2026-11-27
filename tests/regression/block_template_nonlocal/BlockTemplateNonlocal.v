(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   BUG: Block template (%result) IIFE generates [&]() in non-local context.

   When a block template (inline custom with %result) appears in expression
   position inside a static inline initializer, gen_block_iife produces
   [&]() -> Type { ... }() with a capture default. C++ forbids [&] (or any
   capture-default) in non-local lambdas (static/namespace scope).

   The fix would be to use []() instead of [&]() in gen_block_iife, since
   the IIFE body only uses its own local _r variable and global objects
   (like std::cin).
*)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.IO.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** A non-monadic block template *)
Axiom scan_nat_pure : nat.
#[global] Instance scan_nat_pure_mapping : OperationMapping (Ref (@scan_nat_pure)) :=
  pure_cpp ["iostream"] []
    (WithBody "" "std::cin >> %result").

Module BlockTemplateNonlocal.

  (** Block template in pure let binding — compiled to static inline initializer
      with an expression-position IIFE.
      Generates: static inline const unsigned int x = ([&]() -> unsigned int { ... }() + 42u);
      Bug: [&] is invalid in non-local lambda. Should be [](). *)
  Definition pure_block_let : nat :=
    let n := scan_nat_pure in
    n + 42.

  (** Two pure block templates in same expression *)
  Definition two_pure_blocks : nat :=
    let a := scan_nat_pure in
    let b := scan_nat_pure in
    a + b.

End BlockTemplateNonlocal.

Crane Extraction "block_template_nonlocal" BlockTemplateNonlocal.
