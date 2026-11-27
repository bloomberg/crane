(** Found by Ephyra (round 22). Case of case, as in round 1's
    [case_of_case_result_type]: an [if] on a match whose scrutinee is a
    match over [option PrimString.string], one branch of which is itself a
    match on a literal list returning its head ([option]). Expected:
    extracts; [k1 []] picks the [None] head, so it is ["no"] and [ok = true]
    (length 2).

    Fixed: under [CRANE_CHECK_IR] the coercion position check failed: the
    position plan walked the scrutinee of the custom [option] match under
    the function's return type ([string]), but lowering generates a custom
    match's scrutinee under the match's own type ([option<string>]), so the
    coercion of the list head was planned at the string position. The plan
    now walks a custom match's scrutinee as lowering does. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString PrimInt63.
Import ListNotations.
Module CaseOfCaseCoercion.
Definition k1 (l : list nat) : PrimString.string :=
  if match match l with
           | [] => match [@None PrimString.string] with [] => Some ""%pstring | h :: _ => h end
           | _ :: _ => None
           end with Some _ => true | None => false end
  then "yes"%pstring else "no"%pstring.
Definition ok : bool := PrimInt63.eqb (PrimString.length (k1 [])) 2%uint63.
End CaseOfCaseCoercion.
Crane Extraction "case_of_case_coercion" CaseOfCaseCoercion.
