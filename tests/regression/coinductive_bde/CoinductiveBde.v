(** Found by Ephyra (round 21, BDE flavour). A coinductive stream under
    [Mapping.BDE], compiled the way BDE tests are ([scripts/compile-bde.sh],
    [-std=c++20]).

    Expected: compiles; [total = 3 + 4 + 5 + 6 = 18].

    Fixed: two compile errors, both reached by any coinductive type:
    - [theories/cpp/lazy.h] includes [word.h], which read an aggregate's
      fields with a structured binding pack ([auto &[... fs] = x;]), a C++26
      feature.  The runtime now reads an aggregate's fields through
      [aggregate.h], which binds them as a pack under C++26 and counts and
      binds them by name under C++20 ([word.h], [shared_variant.h],
      [shared_block.h] and [crane_bake.h] use it).
    - the generated [lazy_] factory forwarded its thunk with
      [bsl::forward<F>(thunk)], which BDE does not declare; both flavours
      now write [std::forward]. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module CoinductiveBde.
CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint from (n : nat) : stream := SCons n (from (S n)).
Fixpoint take (k : nat) (s : stream) : list nat :=
  match k with O => [] | S k' => match s with SCons x r => x :: take k' r end end.
Definition total : nat := fold_left Nat.add (take 4 (from 3)) 0.
End CoinductiveBde.
Crane Extraction "coinductive_bde" CoinductiveBde.
