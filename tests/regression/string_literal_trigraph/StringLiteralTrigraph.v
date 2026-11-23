(** Found by Ephyra (round 19). A primitive string literal containing a
    trigraph sequence ([??=], [??/], ...).

    Expected: the generated C++ compiles with the test suite's flags and
    [marks] is the three bytes [??=].

    Fixed: the literal was printed as ["??="] and clang rejected it:
    "trigraph ignored [-Werror,-Wtrigraphs]".  The string literal printer
    now escapes a [?] that follows a [?] ([?\?=]).  Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString.

Module StringLiteralTrigraph.

Definition marks : PrimString.string := "??="%pstring.

End StringLiteralTrigraph.

Crane Extraction "string_literal_trigraph" StringLiteralTrigraph.
