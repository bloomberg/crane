(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Test: Effect composition using the real InteractionTrees library.

   Demonstrates two effect types composed with [+'] and automatic
   injection via [inl1]/[inr1].
*)
From Corelib Require Import PrimString.
Require Import Crane.Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

(** ------------------------------------------------------------------ *)
(** Effect types (axiomatized — erased during extraction)               *)
(** ------------------------------------------------------------------ *)

Axiom consoleE : Type -> Type.
Axiom iPrintEndline : string -> consoleE unit.
Axiom iGetLine : consoleE string.

Axiom logE : Type -> Type.
Axiom iLog : string -> logE unit.

(** ------------------------------------------------------------------ *)
(** Combined effect type                                                *)
(** ------------------------------------------------------------------ *)

Definition appE := consoleE +' logE.
Crane Extract Skip appE.

(** ------------------------------------------------------------------ *)
(** Smart constructors (monomorphic, for the concrete appE effect)       *)
(** ------------------------------------------------------------------ *)

Definition print_endline (s : string) : itree appE unit :=
  ITree.trigger (inl1 (iPrintEndline s)).
Definition get_line : itree appE string :=
  ITree.trigger (inl1 iGetLine).
Definition log (s : string) : itree appE unit :=
  ITree.trigger (inr1 (iLog s)).

(** ------------------------------------------------------------------ *)
(** Extraction mappings — inline effect operations to C++               *)
(** ------------------------------------------------------------------ *)

Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'".
Crane Extract Inlined Constant get_line =>
  "[]() -> std::string { std::string s; std::getline(std::cin, s); return s; }()".
Crane Extract Inlined Constant log => "(void)0 /* log: %a0 */".

(** ------------------------------------------------------------------ *)
(** Test programs                                                       *)
(** ------------------------------------------------------------------ *)

Module ITreeEffects.

Definition greet : itree appE unit :=
  log "starting greet" ;;
  print_endline "What is your name?" ;;
  name <- get_line ;;
  print_endline name ;;
  log "finished greet" ;;
  Ret tt.

Definition simple_log : itree appE unit :=
  log "hello" ;;
  log "world" ;;
  Ret tt.

Definition simple_print : itree appE unit :=
  print_endline "line1" ;;
  print_endline "line2" ;;
  Ret tt.

(* Pure computation — no effects *)
Definition pure_value : itree appE nat := Ret 42.

End ITreeEffects.

Crane Extraction "itree_effects" ITreeEffects.
