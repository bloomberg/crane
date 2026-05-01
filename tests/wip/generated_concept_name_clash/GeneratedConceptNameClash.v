From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module MapsTo.

(** Every generated header currently declares a global C++ concept named
    [MapsTo].  If the extracted Rocq module is also named [MapsTo], Crane emits
    both the concept and a struct with the same global C++ name.  The generated
    C++ does not compile because the concept name and struct name collide in the
    same namespace. *)

Definition sample : bool := true.

End MapsTo.

Crane Extraction "generated_concept_name_clash" MapsTo.
