(** Crane emits one struct per library but does not order those structs so
    that a library comes before the libraries that use it.  [Coord] uses
    [Store], yet the generated header declares [struct Coord] first:

      using tbl = List<uint64_t>;

      struct Coord {
        static inline const tbl table_a = Store::build(List<uint64_t>::nil());
      };

      struct Store {
        static tbl build(const List<uint64_t> &t);
      };

    so compiling it gives

      error: use of undeclared identifier 'Store'

    Two controls pin down the trigger.

    Making [table_a] a function instead of a constant still emits the two
    structs in the same wrong order, but compiles, because function bodies are
    emitted out of line after every struct.  Only a constant is exposed, since
    its initialiser runs inside the struct body.

    Annotating [table_a] with [list nat] rather than with [Store]'s alias
    [tbl] makes Crane emit [struct Store] first and the header compiles.  The
    alias is what misleads the ordering: it is hoisted above both structs, so
    it resolves fine on its own, and naming it appears to satisfy [Coord]'s
    dependency on [Store] even though the initialiser also needs [Store]'s
    struct to be complete. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
From Stdlib Require Import List.
From CraneTestsRegression Require Import const_init_forward_ref.Coord.
Import ListNotations.

Definition answer : nat := length table_a.

Crane Extraction "const_init_forward_ref" answer.
