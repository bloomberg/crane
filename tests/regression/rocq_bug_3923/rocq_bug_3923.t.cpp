// Rocq bug #3923: functor extraction leading to uncaught Not_found
// The bug was that extracting a functor with nested module type constraints
// and sealed module applications caused an uncaught Not_found exception.
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.

#include <rocq_bug_3923.h>

int main() {
  // Compilation check only - the bug was about extraction crashing
  return 0;
}
