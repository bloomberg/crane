From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.IO.
From Crane Require Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Local Open Scope pstring_scope.
Local Open Scope itree_scope.
Import ITreeNotations.

Set Crane Loopify.

Module PingPong.

(** Check if two strings are equal using PrimString.compare. *)
Definition string_eq (s1 s2 : string) : bool :=
  match PrimString.compare s1 s2 with
  | Eq => true
  | _ => false
  end.

(** nat_to_string: convert a natural number to a string.
    We only need a simple version for display purposes. *)
Axiom nat_to_string : nat -> string.

(** The game loop.  Corecursive: each iteration prints "ping", reads a
    line, and either loops (if the user said "pong") or terminates.
    The final [Tau] is required by Rocq's productivity checker. *)
CoFixpoint run_game (round : nat) : itree ioE unit :=
  print_endline "ping" ;;
  response <- get_line ;;
  if string_eq response "pong"
  then
    print_endline (cat "  (round " (cat (nat_to_string round) " complete)")) ;;
    Tau (run_game (S round))
  else
    print_endline (cat "You said '" (cat response "' — game over!")) ;;
    Ret tt.

(** Entry point. *)
Definition play : itree ioE unit := run_game 1.

End PingPong.

#[global] Instance nat_to_string_mapping : OperationMapping (Ref (@PingPong.nat_to_string)) :=
  pure_cpp [] ["x0"]
    (Structured (Call "std::to_string" [] [Arg "x0"])).

Crane Extraction "ping_pong" PingPong.
