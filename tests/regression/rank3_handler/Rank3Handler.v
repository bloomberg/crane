From Crane Require Extraction.

(** Polymorphism of rank three: a handler polymorphic in its own type
    argument, a consumer that applies such a handler at two different types,
    and a function that hands a handler to such a consumer.

    Each rank-2 argument is extracted as a polymorphic function object -- a
    lambda with its own [template <typename>] -- because no single
    instantiation would do: [useTwice] applies the same handler at [nat] and
    at [bool]. *)

Inductive reqA (X : Type) : Type := mkA : X -> reqA X.
Arguments mkA {X}.

Notation Handler := (forall X : Type, reqA X -> option X).

(** Rank 2: applies its handler at two types, so a monomorphic argument could
    not stand in for it. *)
Definition useTwice (f : Handler) : option nat :=
  match f nat (mkA 7) with
  | Some n => match f bool (mkA true) with
              | Some true => Some n
              | _ => None
              end
  | None => None
  end.

(** Rank 3: its own argument takes a handler. *)
Definition runWith (k : Handler -> option nat) : option nat :=
  k (fun _ a => match a with mkA x => Some x end).

(** The same rank-3 shape at another result type: the handler [runWith2]
    supplies is the same polymorphic function object, and only the consumer's
    result differs. *)
Definition runWith2 (k : Handler -> option bool) : option bool :=
  k (fun _ a => match a with mkA x => Some x end).

Definition top : option nat := runWith useTwice.

Crane Extraction "rank3_handler" reqA useTwice runWith runWith2 top.
