// Rocq bug #4710: extraction of primitive projections
// The bug was about extracting primitive projections and functions using them.
//
// Bug status in Crane: NOT REPLICATED. Primitive projections and functions
// using them extract and compile correctly.

#include <rocq_bug_4710.h>

#include <cassert>

int main() {
  assert(RocqBug4710::test_bla == 10u);
  assert(RocqBug4710::test_bla_ == true);
  return 0;
}
