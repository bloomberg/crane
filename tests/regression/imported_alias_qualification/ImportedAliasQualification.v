From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import imported_alias_qualification.AliasSource.

(**
  Bug: Imported module type aliases are emitted at top level but referenced
  as nested C++ types in the .cpp file.

  When `cell` is defined as a type alias in AliasSource.v and imported here,
  Crane emits `using cell = std::optional<Player>` at top level in the .h,
  but qualifies it as `AliasSource::cell` in the .cpp return type.
  This produces invalid C++ since `cell` is not a member of `AliasSource`.
*)

Definition entry : AliasSource.cell :=
  AliasSource.id_cell AliasSource.empty_cell.

Crane Extraction "imported_alias_qualification" entry.
