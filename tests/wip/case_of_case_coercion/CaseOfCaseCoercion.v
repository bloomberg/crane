(** Found by Ephyra (round 22). Case of case, as in round 1's
    [case_of_case_result_type] (fixed): an [if] on a match whose scrutinee
    is a match over [option PrimString.string], one branch of which is
    itself a match on a literal list returning its head ([option]).

    Expected: extracts; [k1 []] picks the [None] head, so it is ["no"] and
    [ok = true] (length 2).

    Actual: extraction fails under [CRANE_CHECK_IR]: "Crane IR check
    (coercion position): a coercion in ...k1 is lowered against
    (Corelib.Init.Datatypes.option, 0)<ext:std::string>, the plan's position
    is Corelib.Strings.PrimString.string<>": pushing the outer context into
    the inner branches lowers the head of the [option] list at the string
    position. With [None] in place of the innermost match it extracts. Also
    on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
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
