(** Crane bug, found by Ephyra round 31: a lambda handed to [id] (declared at
    [crane::obj]) whose body calls [fold_right].  The lambda is built in a
    box, and the box's canonical erased shape leaks into the body: the
    receiver and the initial value are [List<crane::obj>::nil()] while the
    folded function takes [List<uint64_t>], "no matching member function for
    call to 'fold_right'".  Only the lambda's result is in the box.
    Expected: [f = 1].  Present at 081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module IdBoxShapeInBody.

Definition f : nat :=
  fold_left (fun a e => a + e)
    ((id (fun _ : nat => fold_right (fun (e : nat) (acc : list nat) => acc) (@nil nat) (@nil nat))) 0) 1.

End IdBoxShapeInBody.

Crane Extraction "id_box_shape_in_body" IdBoxShapeInBody.
