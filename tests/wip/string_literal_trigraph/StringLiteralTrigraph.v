(** Found by Ephyra (round 19). A primitive string literal containing a
    trigraph sequence ([??=], [??/], ...).

    Expected: the generated C++ compiles with the test suite's flags and
    [marks] is the three bytes [??=].

    Actual: the literal is printed as ["??="] and clang rejects it:
    "trigraph ignored [-Werror,-Wtrigraphs]". C++17 removed trigraphs, so
    the value would be right, but the warning is an error under [-Werror];
    the printer should escape the second [?] ([?\?=]). Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString.

Module StringLiteralTrigraph.

Definition marks : PrimString.string := "??="%pstring.

End StringLiteralTrigraph.

Crane Extraction "string_literal_trigraph" StringLiteralTrigraph.
