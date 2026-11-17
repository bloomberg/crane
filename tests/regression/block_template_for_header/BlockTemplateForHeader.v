(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A block template ([%result]) whose text holds a [for] header with an
    empty clause, used as a value.  The printer writes a block's statements
    one per line by splitting it at the semicolons that end them, and used to
    split inside the header too, dropping the empty condition of
    [for (init;; step)].  As a value the block is an immediately invoked
    lambda, which has to capture the locals its arguments read -- and only
    then: a lambda at namespace scope may not have a capture default. *)

From Crane Require Import Mapping.Std Mapping.NatIntStd.

Axiom first_at_least : nat -> nat.
Crane Extract Inlined Constant first_at_least =>
  "for (unsigned int _i = 0;; ++_i) { if (_i >= %a0) { %result = _i; break; } }".

Module BlockTemplateForHeader.

Definition next_after (n : nat) : nat := first_at_least n + 1.

Definition past_ten : nat := first_at_least 10.

End BlockTemplateForHeader.

Crane Extraction "block_template_for_header" BlockTemplateForHeader.
