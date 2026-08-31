(** A loopified function methodified onto a {e template} inductive.  The
    receiver saved in the loop state is declared with the bare template name:

    {v
      cannot form pointer to deduced class template specialization type
      use of class template 'typename List::list' requires template arguments
    v} *)

From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List Arith.

Module LoopifySelfTemplateArgs.

Definition rm (l : list nat) : list nat := remove Nat.eq_dec 2 l.

Definition test : nat := length (rm (cons 1 nil)).

End LoopifySelfTemplateArgs.

Crane Extraction "loopify_self_template_args" LoopifySelfTemplateArgs.
