(** Found by Ephyra round 23 (a probe of [Crane Bake] on rose trees and
    mutual inductives). Reading a baked value whose nodes alternate
    between two types is quadratic: here a 5000-deep chain
    [MAdd (MLit n) (MCons (MAdd ...) MNil)] of the mutual
    [mterm]/[mlist]. The readable image (one node per row) groups rows
    into runs of one type; [reader::run<T>] does
    [tab.reserve(tab.size() + n)] for every run, and alternating types
    make every run one row long, so each row reallocates its type's whole
    table. The same happens for a rose tree ([RNode n [child]]: [rose]
    and [List<rose>] alternate). A same-type chain of 40000 [Node]s reads
    in milliseconds.
    Expected: [result = 5000], read in well under a second.
    Actual: about 7.6 s of CPU before [main] at -O0 (10000 deep: 30 s);
    the test asserts the process used under 2 s of user CPU. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

Module BakeAlternatingTypesQuadratic.

Inductive mterm : Type := MLit : nat -> mterm | MAdd : mterm -> mlist -> mterm
with mlist : Type := MNil : mlist | MCons : mterm -> mlist -> mlist.

Fixpoint alt (n : nat) : mterm :=
  match n with 0 => MLit 0 | S k => MAdd (MLit n) (MCons (alt k) MNil) end.

Definition big : mterm := alt 5000.

Definition result : nat := match big with MAdd (MLit n) _ => n | _ => 0 end.

End BakeAlternatingTypesQuadratic.

Crane Bake BakeAlternatingTypesQuadratic.big.
Crane Extraction "bake_alternating_types_quadratic" BakeAlternatingTypesQuadratic.
