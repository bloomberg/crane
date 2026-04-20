// Rocq bug #4709: extraction wasn't reducing primitive projections in types
// The bug was that primitive projection `foo (Foo nat)` wasn't being reduced
// to `nat` during type extraction, resulting in an unknown type.
//
// Bug status in Crane: NOT REPLICATED. Primitive projection is properly
// reduced to nat and the extracted value has the correct type.

#include <rocq_bug_4709.h>

#include <cassert>

int main() {
  // check should have type nat (reduced from ty = foo (Foo nat))
  assert(RocqBug4709::check == 42u);
  return 0;
}
