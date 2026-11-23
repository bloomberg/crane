(** Found by Ephyra (round 21, BDE flavour). [Crane Bake] under
    [Mapping.BDE], with the BDE root given the way the BDE tests give it
    ([Set Crane BDE Directory "~/..."]). The Reference Manual
    lists [bsl::string] among the types an image holds, so BDE is meant
    to be supported.

    Expected: [table] and [pair] are baked; the program (built with
    [scripts/compile-bde.sh]) prints [6 6].

    Fixed: a chain of failures, each hiding the next:
    - the bake driver was compiled with [-I~/Library/bde_install/include]:
      [Toolchain] did not expand [~] ("'bsl_concepts.h' file not found");
      it now expands a leading [~] to [HOME];
    - the writer's [static_assert] rejected the list constant's
      [bsl::shared_ptr] fields: only [std::shared_ptr] was seen through.  Any
      shared pointer with its interface is now a [detail::handle];
    - the pair alone failed to link: the driver lacked
      [-DBSLS_LIBRARYFEATURES_FORCE_ABI_CPP17] (the ABI the BDE libraries
      are built with), so it referenced an undefined C++20 ABI tag; Crane
      reported only clang's summary line, and now keeps the linker's
      [Undefined symbols] too;
    - [crane_bake.h] (and [shared_variant.h]) used structured binding packs
      and pack indexing, C++26, while BDE programs are built as C++20; they
      now read fields through [aggregate.h], which has a C++20 path.
    The driver also reads the BDE flavour of the runtime headers
    (theories/cpp_bde) ahead of theories/cpp. *)
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
