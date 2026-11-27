(** Found by Ephyra (round 20). [Crane Bake] of a constant whose body is a
    bare primitive string literal ([Mapping.Std]: [std::string]). A variant
    the round-19 fixes ([bake_prim_string], [string_literal_as_char_pointer])
    did not cover: those baked a [cat] and a list of literals.

    Expected: baked; [word = "abc"], [word_ok = true].

    Fixed: the bake driver did not compile ("crane::bake: no way to write a
    value of this type"): the bake unit declared
    [crane::bake::root("abc")], whose template parameter was deduced from
    the literal as [const char*].  The root is now handed over at the
    constant's declared type, [crane::bake::template root<std::string>(...)],
    whatever the initialiser deduces to. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString PrimInt63.
Module BakeStringLiteral.
Definition word : PrimString.string := "abc"%pstring.
Definition word_ok : bool := PrimInt63.eqb (PrimString.length word) 3%uint63.
End BakeStringLiteral.
Crane Bake BakeStringLiteral.word.
Crane Extraction "bake_string_literal" BakeStringLiteral.
