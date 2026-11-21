(** Found by Ephyra (round 19). A tail-recursive function over a list that
    passes a primitive string ([Mapping.Std]) to itself rebuilt with
    [PrimString.sub], under [Set Crane Loopify].

    Expected: [result = 34099] (the string loses its first byte twice: 34
    bytes, the first is 'c' = 99).

    Actual: the string parameter is only read, so it is a [std::string_view]
    (the read view), and Loopify keeps it as a [std::string_view] loop
    variable. The recursive call's argument [crane::string_sub(...)] is a
    fresh [std::string] temporary, and [_loop_s = crane::string_sub(...)]
    leaves the view pointing into it after the statement: clang rejects it
    ("object backing the pointer '_loop_s' will be destroyed at the end of
    the full-expression [-Werror,-Wdangling-assignment-gsl]"); without the
    warning it is a use after free. A loop variable updated with an owned
    value needs the canonical [std::string]. Typed-mappings regression:
    main has no read views and passes the test. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimString.
Import ListNotations.
Set Crane Loopify.
Module LoopifyStringViewDangling.
Definition i2n (i : PrimInt63.int) : nat := Z.to_nat (Uint63.to_Z i).
Definition n2i (n : nat) : PrimInt63.int := Uint63.of_Z (Z.of_nat n).
Fixpoint drop_each (l : list bool) (s : PrimString.string) : nat :=
  match l with
  | [] => i2n (PrimString.length s) * 1000 + i2n (PrimString.get s (n2i 0))
  | _ :: r => drop_each r (PrimString.sub s (n2i 1) (n2i 100))
  end.
Definition result : nat := drop_each [true; true] (PrimString.cat "abcdefghijklmnopqrstuvwxyz"%pstring "0123456789"%pstring).
End LoopifyStringViewDangling.
Eval vm_compute in LoopifyStringViewDangling.result.
Crane Extraction "loopify_string_view_dangling" LoopifyStringViewDangling.
