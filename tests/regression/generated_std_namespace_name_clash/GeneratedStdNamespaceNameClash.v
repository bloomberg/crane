From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module std.

(** Standard extraction includes C++ standard library headers and emits
    references to namespace [std].  If the extracted Rocq module is named [std],
    Crane emits a global C++ struct [std], colliding with the existing standard
    namespace.  The generated C++ does not compile because a namespace and a
    struct cannot share the same name in the global namespace. *)

Definition sample : bool := true.

End std.

Crane Extraction "generated_std_namespace_name_clash" std.
