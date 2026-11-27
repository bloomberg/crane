(** Found by Ephyra (round 19). A primitive string literal (Mapping.Std:
    [std::string]) where C++ deduces the type from the expression.

    Expected: both definitions compile; [nested = 2] (the inner [if] picks
    ["ab"]) and [mapped = 4] (two copies of ["ab"]).

    Fixed: two compile errors, both because the literal was printed as a
    bare ["..."], a [const char*]:
    - [nested]: the match becomes an immediately invoked lambda without a
      return type; one arm returned ["x"] ([const char*]) and another
      [std::string("a") + std::string("b")]: "return type must match
      previous return type".
    - [mapped], under [BoxedFields]: the mapped lambda returned ["ab"], and
      [List<std::string>::Cons] needs a [crane::field<std::string>] from it,
      two user conversions.
    A literal returned from a lambda without a declared return type, or
    bound to an [auto] variable, is now constructed as the string
    ([std::string("x")]).  Also on main. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimString.
Import ListNotations.

Set Crane BoxedFields.

Module StringLiteralAsCharPointer.

Definition len (s : PrimString.string) : nat := Z.to_nat (Uint63.to_Z (PrimString.length s)).

Definition nested : nat :=
  len (match rev [1] with
       | [] => "x"%pstring
       | _ :: _ =>
         if existsb (fun _ => true) [2]
         then PrimString.cat "a"%pstring "b"%pstring
         else "cde"%pstring
       end).

Definition mapped : nat :=
  fold_left (fun a w => a + len w) (map (fun _ : nat => "ab"%pstring) [1; 2]) 0.

End StringLiteralAsCharPointer.

Crane Extraction "string_literal_as_char_pointer" StringLiteralAsCharPointer.
