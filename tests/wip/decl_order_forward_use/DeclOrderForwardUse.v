(** A declaration that a pulled-in stdlib function depends on is emitted after
    the function that mentions it, so the forward declaration does not compile:

    {v
      no template named 'Prod'
    v}

    The same ordering pass also emits [Comparison] after [Nat::compare]. *)

Require Crane.Extraction.

Module DeclOrderForwardUse.

Definition d (a b : nat) : nat := Nat.div a b.

Definition test : nat := d 7 2.

End DeclOrderForwardUse.

Crane Extraction "decl_order_forward_use" DeclOrderForwardUse.
