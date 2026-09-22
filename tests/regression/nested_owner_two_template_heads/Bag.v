From Crane Require Import Mapping.Std.

(** Named after the inductive, and file-level, so its declarations are written
    in the wrapper struct the inductive is written under -- the collision that
    keeps the two names apart.

    Nothing here takes a [bag], so nothing here is promoted onto the datatype
    and everything stays beside it in the wrapper.  [Use.v] has to name this,
    though: a declaration nothing reaches is never emitted, and a wrapper whose
    only child is the datatype is written as one struct with it -- which is the
    other branch, and one that also compiles, out-lines, and takes two template
    heads.  What distinguishes them is that

      grep -o '\bBag::[a-zA-Z_][A-Za-z_0-9]*' nested_owner_two_template_heads.h

    names something besides [Bag::bag]. *)
Definition depth_limit : nat := 8.
