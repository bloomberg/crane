(** Found by Ephyra (round 20). [Crane Bake] of a constant whose body is a
    bare primitive string literal ([Mapping.Std]: [std::string]). A variant
    the round-19 fixes ([bake_prim_string], [string_literal_as_char_pointer])
    did not cover: those baked a [cat] and a list of literals.

    Expected: baked; [word = "abc"], [word_ok = true].

    Actual: the bake driver does not compile: "static assertion failed due
    to requirement 'dependent_false<const char *>': crane::bake: no way to
    write a value of this type". The bake unit declares
    [static inline const std::string word = crane::bake::root("abc");], and
    [root]'s template parameter is deduced from the bare literal as
    [const char*] rather than the declared [std::string]. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString PrimInt63.
Module BakeStringLiteral.
Definition word : PrimString.string := "abc"%pstring.
Definition word_ok : bool := PrimInt63.eqb (PrimString.length word) 3%uint63.
End BakeStringLiteral.
Crane Bake BakeStringLiteral.word.
Crane Extraction "bake_string_literal" BakeStringLiteral.
