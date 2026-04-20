// Rocq bug #14843: record projection name conflicts with module definitions
// The bug was that record projections (f1, f2) conflicting with module
// definitions of the same name caused incorrect renaming.
//
// Bug status in Crane: NOT REPLICATED. Name conflicts between record
// projections and module definitions are handled correctly.

#include <rocq_bug_14843.h>

int main() {
  // Compilation check - the name conflict should be handled correctly
  return 0;
}
