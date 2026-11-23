(** Found by Ephyra (round 19). [PrimString.make] and [PrimString.compare]
    under [Mapping.Std], which maps Rocq's primitive [string] to
    [std::string].

    Expected: [make 3 0] is three NUL bytes (its length is 3) and
    [compare "ab" "b"] is [Lt]; the program prints [1 1 1 1 1 1].

    Fixed: the C++ threw at static initialisation: "unrealized axiom:
    Corelib.Strings.PrimString.make" (and [compare]).  [Mapping.Std] mapped
    only [length], [cat], [get] and [sub]; [make], [compare] and
    [max_length] are now mapped too ([Mapping.BDE] likewise), with Rocq's
    semantics: [make] clamps the length to [max_length] and the character
    to its low byte, [compare] is lexicographic on unsigned bytes.  Also on
    main (legacy [Mapping.Std]).  The other cases check each of these
    against Rocq ([Eval] below: all [true]). *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString PrimInt63.
Open Scope uint63_scope.

Module PrimStringMakeCompare.

Definition nuls : PrimString.string := PrimString.make 3 0.

Definition nul_length : bool := PrimInt63.eqb (PrimString.length nuls) 3.

Definition cmp_lt : bool :=
  match PrimString.compare "ab"%pstring "b"%pstring with Lt => true | _ => false end.

(** [make] clamps its length to [max_length] and its character to the
    low byte: [make (max_length + 5) 300] is [max_length] bytes of 44. *)
Definition max_length_value : bool := PrimInt63.eqb PrimString.max_length 16777211.

Definition make_clamped : bool :=
  let s := PrimString.make (PrimInt63.add PrimString.max_length 5) 300 in
  andb (PrimInt63.eqb (PrimString.length s) PrimString.max_length)
       (PrimInt63.eqb (PrimString.get s 7) 44).

(** [compare] reads bytes unsigned: a byte of 200 is above ["a"]; a proper
    prefix is below; equal strings are [Eq]. *)
Definition cmp_high_gt : bool :=
  match PrimString.compare (PrimString.make 1 200) "a"%pstring with Gt => true | _ => false end.

Definition cmp_prefix : bool :=
  match PrimString.compare "abc"%pstring "ab"%pstring, PrimString.compare "ab"%pstring "ab"%pstring with
  | Gt, Eq => true
  | _, _ => false
  end.

End PrimStringMakeCompare.

Eval vm_compute in
  (PrimStringMakeCompare.nul_length, PrimStringMakeCompare.cmp_lt,
   PrimStringMakeCompare.max_length_value, PrimStringMakeCompare.make_clamped,
   PrimStringMakeCompare.cmp_high_gt, PrimStringMakeCompare.cmp_prefix).

Crane Extraction "prim_string_make_compare" PrimStringMakeCompare.
