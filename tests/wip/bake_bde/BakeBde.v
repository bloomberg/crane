(** Found by Ephyra (round 21, BDE flavour). [Crane Bake] under
    [Mapping.BDE], with the BDE root given the way the BDE tests give it
    ([Set Crane BDE Directory "~/..."]). docs/Crane-Bake.md lists
    [bsl::string] in the image format, so BDE is meant to be supported.

    Expected: [table] and [pair] are baked; the program (built with
    [scripts/compile-bde.sh]) prints [6 6].

    Actual: a chain of failures, each hiding the next:
    - the bake driver is compiled with [-I~/Library/bde_install/include]:
      [Toolchain] does not expand [~], so "fatal error: 'bsl_concepts.h'
      file not found";
    - with an absolute directory, the list constant fails the writer's
      [static_assert] ("dependent_false<bsl::shared_ptr<List<unsigned
      int>>>: no way to write a value of this type"): only [std::shared_ptr]
      fields are seen through;
    - with an absolute directory, the pair alone fails to link ("linker
      command failed"; Crane reports only clang's summary line);
    - [crane_bake.h] (and [shared_variant.h]) use structured binding packs
      and pack indexing, C++26, while BDE programs are built as C++20.
    Typed-mappings ([Crane Bake] is new on the branch). *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Set Crane BDE Directory "~/Library/bde_install/".

Module BakeBde.

Definition table : list nat := [1; 2; 3].

Definition pair : nat * nat := (1, 5).

Definition total : nat := fold_left Nat.add table 0.

Definition pair_sum : nat := fst pair + snd pair.

End BakeBde.

Crane Bake BakeBde.table BakeBde.pair.

Crane Extraction "bake_bde" BakeBde.
