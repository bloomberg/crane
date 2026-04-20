// Rocq bug #13453: extraction of primitive arrays
// The bug was about extracting Rocq primitive arrays (#array_type).
// Primitive arrays are a kernel-level feature that may not be supported
// by all extraction backends.
//
// Bug status in Crane: NOT REPLICATED. Primitive array extraction compiles.

#include <rocq_bug_13453.h>

int main() {
  // Compilation check only
  return 0;
}
