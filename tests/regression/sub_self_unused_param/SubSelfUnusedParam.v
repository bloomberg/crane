(** Found by Ephyra round 24, a variant left by the fix of round 3's
    [sub_self_guard_werror] (which folds [a - a] to [0]): when [a] is the
    only field read from a [match] on a parameter of a user inductive, the
    fold left the match binding nothing, so the printer wrote its branch
    alone, but the parameter kept its name:
    [uint64_t g1(const box &b) { return 0; }] tripped [-Wunused-parameter]
    under the suite's [-Werror].  Fixed: the variables a body's text reads
    ([Cpp_ir.Written]) no longer count the scrutinee of a match of one
    constructor, exhaustive, that binds nothing, which the printer does
    not write.

    - [on_box]: a one-constructor inductive.
    - [on_stream]: a coinductive, the shape the generator found.
    - [in_branch]: the match under another branch.

    Expected: compiles with [-Werror]; [on_box (Box 5) = 0],
    [in_branch true (Box 5) = 0], [in_branch false (Box 5) = 7]. *)
From Crane Require Import Mapping.NatInt.
From Crane Require Import Extraction.

Module SubSelfUnusedParam.

Inductive box : Type := Box (n : nat).

CoInductive stream : Type := SCons : nat -> stream -> stream.

CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).

Definition on_box (b : box) : nat := match b with Box a => a - a end.

Definition on_stream (s : stream) : nat := match s with SCons h _ => h - h end.

Definition in_branch (c : bool) (b : box) : nat :=
  match c with true => match b with Box a => a - a end | false => 7 end.

Definition result : nat := on_box (Box 5) + on_stream (sconst 3) + in_branch false (Box 5).

End SubSelfUnusedParam.

Crane Extraction "sub_self_unused_param" SubSelfUnusedParam.
