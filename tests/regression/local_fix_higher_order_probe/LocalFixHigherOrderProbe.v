From Crane Require Extraction.

Module LocalFixHigherOrderProbe.

Definition sample (n : nat) : nat :=
  let fix go (k : nat -> nat) (n : nat) : nat :=
      match n with
      | 0 => k 0
      | S n' => go (fun x => k (S x)) n'
      end in
  go (fun x => x) n.

Definition run : nat := sample 3.

End LocalFixHigherOrderProbe.

Crane Extraction "local_fix_higher_order_probe" LocalFixHigherOrderProbe.
