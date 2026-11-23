(** Found by Ephyra (round 21, BDE flavour). A local fixpoint returning
    a pair, inlined into a constant, under [Mapping.BDE].

    Expected: compiles; [result = 4].

    Fixed: "return type 'bsl::pair<unsigned int, List<unsigned int>>' must
    match previous return type 'pair<...>'".  Pairs were spelled
    [bsl::pair] in declarations but built with [bsl::make_pair], which under
    this BDE build (C++17 ABI) is [std::make_pair] and returns a
    [std::pair]: an immediately invoked lambda returning both a built pair
    and a declared one had two return types (and under [BoxedFields] a
    [crane::field<bsl::pair<...>>] could not take the built one).
    [Mapping.BDE] now builds a pair at its declared type,
    [bsl::pair<A, B>(a, b)]. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module PairMixBde.
Definition result : nat :=
  fst (let fix go (l : list bool) (acc : nat * list nat) {struct l} : nat * list nat :=
         match l with [] => (4, []) | _ :: _ => acc end in
       go [] (1, [])).
End PairMixBde.
Crane Extraction "pair_mix_bde" PairMixBde.
