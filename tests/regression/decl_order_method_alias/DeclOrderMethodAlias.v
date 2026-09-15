From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
From CraneTestsRegression Require Import decl_order_method_alias.RegFile.
Import ListNotations.

(**
  A top-level inductive's sibling function whose type names the file's type
  alias and whose body calls another function of the same file.

  [write_r] stays a static function of [struct RegFile] instead of becoming
  an inline method of [struct Rv]: the alias [rfile] and
  [RegFile::replace_nth] are both declared after [struct Rv]. Crane used to
  make it a method, and the header did not compile.
*)

Definition written : option rfile := write_r [RU; RS 1; RU] 1 (RS 7).

Definition written_second : nat :=
  match written with
  | Some (_ :: RS n :: _) => n
  | _ => 0
  end.

Definition out_of_range : bool :=
  match write_r [RU] 5 RU with
  | None => true
  | Some _ => false
  end.

Crane Extraction "decl_order_method_alias" written_second out_of_range.
