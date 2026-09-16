(** Crane bug: a constructor whose lowercased name is a C library macro is
    emitted unguarded, so the preprocessor eats the declaration.

    [Alloca] becomes the smart constructor

      static Request alloca(Nat size, Nat align, bool zeroed) { ... }

    and <alloca.h> -- which Crane's own prelude pulls in transitively --
    defines [alloca] as a one-argument function-like macro.

    Expected: the name is mangled, or [alloca] is #undef'd in the prologue.
    Actual:   error: too many arguments provided to function-like macro invocation
              note: macro 'alloca' defined here (alloca.h:42)
              error: expected expression
              error: expected ';' at end of declaration list

    Three arguments are needed to get the "too many arguments" diagnostic; at
    one argument the call expands silently into [__alloca].

    Seen in Vellvm on [MemoryE]'s [Alloca] event: 3 macro errors plus, further
    down, "too few template arguments for variable template 'alloca'" at every
    call site, because the declaration never survived. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Variant request : Set :=
  | Alloca (size : nat) (align : nat) (zeroed : bool)
  | Free (addr : nat).

Module CMacroName.

  Definition example : request := Alloca 8 1 true.

End CMacroName.

Crane Extraction "c_macro_name" CMacroName.
