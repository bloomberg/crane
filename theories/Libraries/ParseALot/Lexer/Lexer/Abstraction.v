(* SPDX-License-Identifier: BSD-3-Clause *)
From Crane.Libraries.ParseALot.Lexer Require Import State.

(** Module type specifying the interface for a correct lexer over a given state type. *)
Module Type Lexer (STT : State.T).

  Export STT.Defs.
  Export STT.R.Defs.
  Export STT.Ty.

  (** Runs the lexer on [code] using [rules], returning the token list and unconsumed suffix. *)
  Parameter lex : list Rule -> String -> list Token * String.

  (** Soundness: if [lex] returns [(ts, rest)] then [tokenized] holds, given functional rules. *)
  Parameter lex_sound :  forall ts code rest rus,
      lex rus code = (ts, rest)
      -> rules_is_function rus
      -> tokenized rus code ts rest.

  (** Completeness: if [tokenized] holds then [lex] returns the unique matching result. *)
  Parameter lex_complete : forall ts code rest rus,
      tokenized rus code ts rest
      -> rules_is_function rus
      -> lex rus code = (ts, rest).

End Lexer.
