(* Rocq bug #11114: indexed inductive with record and extraction implicit *)

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RocqBug11114.

Inductive t (sig : list nat) :=
| T (k : nat).

Record pkg :=
  { _sig : list nat;
    _t : t _sig }.

Definition map (f : nat -> nat) (p : pkg) :=
  {| _sig := p.(_sig);
     _t := match p.(_t) with
          | T _ k => T p.(_sig) (f k)
          end |}.


Definition test_pkg := {| _sig := cons 1 nil; _t := T _ 2 |}.
Definition test_map := map (fun x => x + 1) test_pkg.

End RocqBug11114.

Crane Extraction "rocq_bug_11114" RocqBug11114.
