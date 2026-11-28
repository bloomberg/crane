(** Crane bug, found by Ephyra round 31: [id] (declared at [crane::obj])
    applied to a function that eta-reduces to a method, [fun l => length l].
    The method is passed as its value lambda, [[](const List<uint64_t> &_x)
    { return _x.length(); }], boxed as it is rather than through
    [crane_erase_fn], so the box holds no [crane::fn<crane::obj(crane::obj)>]
    and recovering the callable throws [bad_any_cast].  Expected: [g = 2].
    Present at 081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module IdMethodValueUnerased.

Definition g : nat := (id (fun l : list nat => length l)) [4; 5].

End IdMethodValueUnerased.

Crane Extraction "id_method_value_unerased" IdMethodValueUnerased.
