(** Found by Ephyra (round 21, BDE flavour). A local fixpoint returning
    a pair, inlined into a constant, under [Mapping.BDE].

    Expected: compiles; [result = 4].

    Actual: compile error "return type 'bsl::pair<unsigned int,
    List<unsigned int>>' must match previous return type
    'pair<__unwrap_ref_decay_t<unsigned int>, ...>'". Pairs are spelled
    [bsl::pair] in declarations but built with [bsl::make_pair], which under
    this BDE build (C++17 ABI) is [std::make_pair] and returns a
    [std::pair]: an immediately invoked lambda returning both a built pair
    and a declared one has two return types. The same mix shows under
    [BoxedFields] as "no viable conversion from 'pair<...>' to
    'crane::field<bsl::pair<...>>'". Also on main. *)
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
