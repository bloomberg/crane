From Crane Require Import Mapping.Std.
From Crane Require Extraction.

(** A record named, up to case, like the file that declares it.  Under
    separate extraction the file is a namespace, so the record is not merged
    into it: [first_twice] calls [first] as the free function it is. *)
Record cfg (T : Type) := mk_cfg { init : T; rest : list T }.

Definition first {T} (c : cfg T) : T := init _ c.
Definition first_twice {T} (c : cfg T) : T * T := (first c, first c).
