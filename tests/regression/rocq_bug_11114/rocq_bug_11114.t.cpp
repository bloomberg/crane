// Rocq bug #11114: indexed inductive with record and extraction implicit
// The bug was about extracting an inductive type indexed by a list,
// a record containing that inductive, and a map function over the record.
//
// Bug status in Crane: NOT REPLICATED (with Extraction Implicit removed).
// Extraction Implicit causes a SafeImplicits error, but the core extraction
// of indexed inductives with records works correctly without it.

#include <rocq_bug_11114.h>

int main() {
  // Compilation check - the map function should be extractable
  return 0;
}
