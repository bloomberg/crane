// Rocq bug #14100: extraction of variant/inductive types assigned to
// module type parameters.
// The bug was that extracting a module where a variant type is assigned
// to a module type parameter caused issues.
//
// Bug status in Crane: DIFFERENT BUG. Extraction succeeds but generated C++
// fails with: "static_assert(MinSIG<Min>)" - the concept MinSIG does not
// match the Min struct. The variant type assigned to a module type parameter
// generates an incorrect concept constraint.

#include <rocq_bug_14100.h>

int main() {
  // Compilation check only
  return 0;
}
