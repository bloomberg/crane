// Rocq bug #4720: extraction and "with" in module type
// The bug was that module type constraints with "with Module" and
// "with Definition" caused Anomaly or Assert Failure in extraction.
//
// Bug status in Crane: DIFFERENT BUG. Extraction succeeds but generated C++
// is invalid. The concept constraints for functors with "with Module" and
// "with Definition" generate incorrect template parameter syntax:
//   "requires A<typename M::a>" is not valid C++ concept syntax.

#include <rocq_bug_4720.h>

int main() {
  // Compilation check only - the bug was about extraction crashing
  return 0;
}
