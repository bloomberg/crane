From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Crane Require Extraction.
From CraneTestsWIP Require Import file_module_eponymous_record.Catalog.

(**
  Bug: a record named like its file module loses its name.

  [catalog] is defined in Catalog.v. The header declares it as [struct;]
  and defines it as [struct { ... };], and the functions of [struct Catalog]
  take [const &c]. The header does not compile.

  The same record inside an explicit [Module Catalog] in one file extracts
  correctly, as does a record named [catalogue] in Catalog.v.
*)

Definition answer : nat := size (grow {| size := 1 |}).

Crane Extraction "file_module_eponymous_record" answer.
