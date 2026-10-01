(* When a nested module's name collides with a type name, Crane folds the
   module into a struct named after the *file*.  The file's own top-level
   definitions are emitted as members of that same struct, so a reference to
   one has to name the struct: [Helpers::map_monad], exactly as a member that
   came from the nested module is spelled.  Registering only the wrapped
   children left the two halves of one struct spelled differently, and the
   file's own half came out with an empty qualifier, [::map_monad].

   In Vellvm this was the single largest cluster, 76 errors: [map_monad],
   [vec_loop], [loop_monad], [repeatN], [N_length], [N_to_nat_safe]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.
From Stdlib Require Import List NArith.
From CraneTestsRegression Require Import Helpers.

Module FileStructEmptyQualifier.
  (* Correctly qualified: comes from the folded [Module N]. *)
  Definition a (l : list nat) : N := Helpers.N.length l.

  (* Empty qualifier: comes from the file's own top level. *)
  Definition b (l : list nat) : option (list nat) :=
    Helpers.map_monad option (M := Monad_option) (fun x => Some (S x)) l.
End FileStructEmptyQualifier.

Crane Extraction "file_struct_empty_qualifier" FileStructEmptyQualifier.
