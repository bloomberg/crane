From Corelib Require Import PrimInt63 PrimArray.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module persistent_array.

(** The [PrimArray] mapping includes the C++ runtime helper
    [persistent_array<T>] in the global namespace.  If the extracted Rocq module
    is also named [persistent_array], Crane emits a global C++ struct with the
    same name as the runtime class template.  The generated C++ does not compile
    because the helper template and extracted module struct collide. *)

Definition arr : array bool := PrimArray.make 1%int63 true.
Definition sample : bool := PrimArray.get arr 0%int63.

End persistent_array.

Crane Extraction "generated_persistent_array_name_clash" persistent_array.
