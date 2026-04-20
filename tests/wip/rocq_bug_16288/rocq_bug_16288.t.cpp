// Rocq bug #16288: extraction of primitive projections within a functor
// were incorrectly referencing themselves.
// The bug was that primitive projection extraction inside a functor
// generated self-referencing code.
//
// Bug status in Crane: DIFFERENT BUG. Extraction succeeds but generated C++
// fails with: "use of undeclared identifier 'Empty'". The functor
// instantiation M' := M(Empty) references Empty outside its scope.
// The Empty module struct is not emitted or is in the wrong scope.

#include <rocq_bug_16288.h>

int main() {
  // Compilation check only
  return 0;
}
