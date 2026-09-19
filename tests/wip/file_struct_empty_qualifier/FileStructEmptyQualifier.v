(* When a nested module's name collides with a type name, Crane folds the
   module into a struct named after the *file*.  The file's own top-level
   definitions are then emitted as members of that same struct -- but call
   sites still qualify them as if they were at namespace scope, producing an
   empty qualifier [::map_monad].  Members that came from the nested module
   are qualified correctly, so the two halves of one struct disagree.

   Expected: [Helpers::template map_monad<Monad_option, Nat, Nat>(...)]
   Actual:   [::template map_monad<Monad_option, Nat, Nat>(...)]
             error: no template named 'map_monad' in the global namespace;
                    did you mean 'Helpers::map_monad'?

   In Vellvm this is the single largest cluster: 76 errors.  [struct ListUtil]
   opens at vellvm_bench.h:3081 and [map_monad] is a member at :3186, yet every
   cross-file reference spells it [::template map_monad<...>].  The members
   that came from [Module N] ([length], [length_acc]) are spelled correctly.
   Same shape for vec_loop, loop_monad, repeatN, N_length, N_to_nat_safe. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Data.Monads.OptionMonad.
From Stdlib Require Import List NArith.
From CraneTestsWIP Require Import Helpers.

Module FileStructEmptyQualifier.
  (* Correctly qualified: comes from the folded [Module N]. *)
  Definition a (l : list nat) : N := Helpers.N.length l.

  (* Empty qualifier: comes from the file's own top level. *)
  Definition b (l : list nat) : option (list nat) :=
    Helpers.map_monad option (M := Monad_option) (fun x => Some (S x)) l.
End FileStructEmptyQualifier.

Crane Extraction "file_struct_empty_qualifier" FileStructEmptyQualifier.
