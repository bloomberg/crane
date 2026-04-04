(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests effect operations used across module boundaries.
   Verifies that type class instance resolution and effect erasure
   work correctly when effects are defined in inner modules.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module EffectCrossModule.

(** Inner module defines a helper that returns a value *)
Module Inner.
  Definition greet (name : string) : itree ioE unit :=
    print_endline (cat "Hello, " name).

  Definition ask_name : itree ioE string :=
    print_endline "What is your name?" ;;
    get_line.

  (** Function taking a callback *)
  Definition with_greeting {A : Type} (f : string -> itree ioE A) : itree ioE A :=
    name <- ask_name ;;
    greet name ;;
    f name.
End Inner.

(** Outer code uses Inner's definitions *)
Definition test_greet : itree ioE unit :=
  Inner.greet "world".

Definition test_ask_name : itree ioE string :=
  Inner.ask_name.

Definition test_with_greeting : itree ioE int :=
  Inner.with_greeting (fun name => Ret (PrimString.length name)).

(** Use Inner's helper in a recursive function *)
Fixpoint greet_all (names : list string) : itree ioE unit :=
  match names with
  | nil => Ret tt
  | cons name rest =>
    Inner.greet name ;;
    greet_all rest
  end.

(** Use two effects from different modules *)
Definition combined_io_op : itree ioE string :=
  name <- Inner.ask_name ;;
  write_file "last_name.txt" name ;;
  Ret name.

End EffectCrossModule.

Crane Extraction "effect_cross_module" EffectCrossModule.
