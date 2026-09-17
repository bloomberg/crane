(** Crane bug: the forward declarations of concept-constrained instances are
    emitted before the concepts they refer to.

    [Functor_Monad] is a template constrained by [Monad]:

       17 | template <Monad _tcI0> struct Functor_Monad;   // forward decl
      120 | concept Monad = requires { ... };
      167 | template <Monad _tcI0> struct Functor_Monad { ... };

    At line 17 [Monad] is not yet a name, so clang reads [_tcI0] as a
    *non-type* parameter of unknown type; the real definition at 167 then
    disagrees with it.

    Expected: the forward-declaration block comes after the concepts, or a
              constrained instance is not forward-declared at all.
    Actual:   error: unknown type name 'Monad'
              error: template parameter has a different kind in template
                     redeclaration
              error: template argument for non-type template parameter must be
                     an expression

    Seen in Vellvm as one block of forward declarations at lines 18-26 naming
    six concepts that are all declared later -- [Monad], [Provenance],
    [Pointer], [PI], [IPtr], [Params]: 13 "unknown type name" plus 11
    "different kind in template redeclaration". *)

From Crane Require Extraction.
From ExtLib Require Import Structures.Monads Structures.Functor.

(* An instance parameterised by another class's instance: its C++ struct is a
   template constrained by the concept [Monad]. *)
#[global] Instance Functor_Monad (M : Type -> Type) `{Monad M} : Functor M :=
  { fmap := fun A B f x => bind x (fun a => ret (f a)) }.
