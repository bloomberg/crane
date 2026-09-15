From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
From CraneTestsRegression Require Import decl_order_method_call.Regs.
Import ListNotations.

(**
  As decl_order_method_alias, but without the type alias.

  [write_r] calls [Regs::replace_nth], so it stays a static function of
  [struct Regs]: as an inline method of [struct Rv] it would call into a
  struct declared after it. Crane used to make it a method; the call alone
  was enough to break the header.
*)

Definition written_second : nat :=
  match write_r [RU; RS 1; RU] 1 (RS 7) with
  | Some (_ :: RS n :: _) => n
  | _ => 0
  end.

Definition out_of_range : bool :=
  match write_r [RU] 5 RU with
  | None => true
  | Some _ => false
  end.

Crane Extraction "decl_order_method_call" written_second out_of_range.
