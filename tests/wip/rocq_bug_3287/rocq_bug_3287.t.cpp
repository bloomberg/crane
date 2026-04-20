// Rocq bug #3287: extraction of module with logical parts (I,I)
// The bug was that a module containing logical values like (I,I) : (True * True)
// caused extraction issues. The test checks that bar values from both modules
// (with and without logical parts) extract correctly.
//
// Bug status in Crane: REPLICATED. Extraction fails with:
//   "The informative inductive type prod has a Prop instance."
// Same error as in Rocq's OCaml extraction. The module containing
// (I,I) : (True * True) : Prop triggers a sort-polymorphism issue.

#include <rocq_bug_3287.h>

#include <cassert>

int main() {
  assert(RocqBug3287::bar1 == true);
  assert(RocqBug3287::bar2 == true);
  return 0;
}
