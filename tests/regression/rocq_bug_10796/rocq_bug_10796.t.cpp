// Rocq bug #10796: extraction inside a module
// The bug was that Separate Extraction inside a module didn't work correctly.
// We test that a simple definition extracted from inside a module works.
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.

#include <rocq_bug_10796.h>

#include <cassert>

int main() {
  assert(RocqBug10796::a == 0u);
  return 0;
}
