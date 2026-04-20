// Rocq bug #20894: extraction of axiom with sealed module type
// The bug was about extracting an axiom whose type comes from a
// sealed module (Module M : S), where the implementation details
// are hidden by the module type.
//
// Bug status in Crane: NOT REPLICATED. Axiom with sealed module type
// extracts and compiles correctly.

#include <rocq_bug_20894.h>

int main() {
  // Compilation check only
  return 0;
}
