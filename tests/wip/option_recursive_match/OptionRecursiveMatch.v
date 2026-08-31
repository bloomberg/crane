(** An inductive that recurses through [option], pattern-matched recursively.
    [option] is mapped to [std::optional], but the match still dispatches on it
    as if it were a Crane inductive:

    {v
      no type named 'Some' in 'std::optional<OptionRecursiveMatch::chain>'
    v} *)

Require Crane.Extraction.

Module OptionRecursiveMatch.

Inductive chain := C : nat -> option chain -> chain.

Fixpoint len (c : chain) : nat :=
  match c with C _ None => 1 | C _ (Some r) => S (len r) end.

Definition test : nat := len (C 1 (Some (C 2 None))).

End OptionRecursiveMatch.

Crane Extraction "option_recursive_match" OptionRecursiveMatch.
