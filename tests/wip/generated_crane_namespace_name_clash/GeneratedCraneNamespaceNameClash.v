From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module crane.

(** Coinductive extraction includes [lazy.h], which declares namespace [crane].
    If the extracted Rocq module is also named [crane], Crane emits a global
    C++ struct [crane] in the same namespace scope.  The generated C++ does not
    compile because a namespace and a struct cannot share the same global name. *)

CoInductive stream : Type :=
| Cons : bool -> stream -> stream.

CoFixpoint ones : stream := Cons true ones.

Definition head (s : stream) : bool :=
  match s with
  | Cons b _ => b
  end.

Definition sample : bool := head ones.

End crane.

Crane Extraction "generated_crane_namespace_name_clash" crane.
