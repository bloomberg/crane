// Rocq bug #20989: extraction of module alias through functor application
// The bug was about extracting a module created by functor application
// (Module N := M(A)) where the functor uses module aliases (Module In := X).
//
// Bug status in Crane: NOT REPLICATED. Module alias through functor
// application extracts and compiles correctly.

#include <rocq_bug_20989.h>

#include <cassert>

int main() {
  assert(RocqBug20989::N::n() == 0u);
  return 0;
}
