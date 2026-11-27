(** Found by Ephyra round 23 (a probe of [Crane Bake] on rose trees and
    mutual inductives). A baked value whose nodes alternate between two
    types: a 50000-deep chain [MAdd (MLit n) (MCons (MAdd ...) MNil)] of
    the mutual [mterm]/[mlist], 150000 nodes. The same holds for a rose
    tree ([RNode n [child]]: [rose] and [List<rose>] alternate).
    Expected: [result = 50000], read in well under a second (the test
    asserts under 1 s of user CPU before [main], at -O0).
    Fixed: reading was quadratic, about 7.6 s for a 5000-deep chain. The
    readable image (one node per row) groups rows into runs of one type,
    and [reader::run<T>] did [tab.reserve(tab.size() + n)] for every run:
    alternating types make every run one row long, so each row copied its
    type's whole table. The table now grows as a vector does. Writing gave
    every run's header a comment past the first 1000 rows, so the image
    was five times larger than needed (30 MB for 100000 deep); a header is
    now bare there, as rows are. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

Module BakeAlternatingTypesQuadratic.

Inductive mterm : Type := MLit : nat -> mterm | MAdd : mterm -> mlist -> mterm
with mlist : Type := MNil : mlist | MCons : mterm -> mlist -> mlist.

Fixpoint alt (n : nat) : mterm :=
  match n with 0 => MLit 0 | S k => MAdd (MLit n) (MCons (alt k) MNil) end.

Definition big : mterm := alt 50000.

Definition result : nat := match big with MAdd (MLit n) _ => n | _ => 0 end.

End BakeAlternatingTypesQuadratic.

Crane Bake BakeAlternatingTypesQuadratic.big.
Crane Extraction "bake_alternating_types_quadratic" BakeAlternatingTypesQuadratic.
