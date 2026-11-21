(** A partial application of a functor's member, under separate extraction,
    whose callee's signature names an alias the call's own types do not.

    [LX.lex] (Inst.v, an application of [LexFn] from Lib.v) returns
    [list LX.D.Token * list nat], [Token] an alias of [nat * nat].  Here
    [LX.lex [1; 2; 3]] is handed to [SL.lex_with] and eta-expanded into a
    lambda whose return type is read off [LX.lex]'s signature, naming
    [Inst::LX::D::Token].  Reduced from a higher-order [lex_sem_with] variant
    of ParseALot's lexer hoist ([lex_sem_with (lex_M_pre json_srules)]), which
    hit the same anomaly at [LXR.Mem.STT.Defs.Coredefs.Token].

    Expected: compiles; [result = 3].

    Fixed: anomaly "Crane: a declaration names the type head of
    ...Inst.LX.D.Token, which resolving it did not ask for.".  The names a
    unit refers to were planned from its Core terms and types, where the
    alias is unfolded, and from a callee's signature only for a member of a
    functor parameter; a call is written against every callee's signature,
    which is now walked for each. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
From CraneTestsRegression Require Import sep_ext_callee_alias_type_head.Lib.
From CraneTestsRegression Require Import sep_ext_callee_alias_type_head.Inst.

Definition lex_rules := SL.lex_with (LX.lex [1; 2; 3]).
Definition result : nat := lex_rules [4].
Crane Separate Extraction result.
