From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

(** An enum eponymous with the module that is extracted is not promoted into
    the module's struct: it stays an [enum class] member, and the module's
    other definitions stay members beside it.  Promoting it wrote
    [struct EponymousEnumModule { enum class EponymousEnumModule {...}; }],
    a member named like its class, and dropped every other definition. *)
Module EponymousEnumModule.

Inductive eponymousEnumModule := Red | Green | Blue.

Definition next (c : eponymousEnumModule) : eponymousEnumModule :=
  match c with
  | Red => Green
  | Green => Blue
  | Blue => Red
  end.

Definition is_red (c : eponymousEnumModule) : bool :=
  match c with
  | Red => true
  | _ => false
  end.

End EponymousEnumModule.

Crane Extraction "eponymous_enum_module" EponymousEnumModule.
