// Rocq bug #5177: extraction and module type containing application
// and "with". The bug was that extracting a functor with a constrained
// output type using "with Definition" caused errors.
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.

#include <rocq_bug_5177.h>

int main() {
  // Compilation check only - the bug was about extraction crashing
  return 0;
}
