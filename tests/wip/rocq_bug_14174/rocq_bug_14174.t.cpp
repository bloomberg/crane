// Rocq bug #14174: extraction error with sort-polymorphic singleton
// inductive types having Prop instances (sig2).
// The bug was that extracting Corelib.Init.Specif caused an error about
// sort-polymorphic singleton inductive types with logical parameters.
//
// Bug status in Crane: DIFFERENT BUG. Extraction succeeds but generated C++
// references undefined type 'Coq__1': "using SigTNotations = Coq__1".
// The Coq__1 renaming prefix (from legacy Coq naming) is used but the
// corresponding struct is never defined.

#include <rocq_bug_14174.h>

int main() {
  // Compilation check only
  return 0;
}
