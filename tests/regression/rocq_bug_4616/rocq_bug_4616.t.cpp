// Rocq bug #4616: primitive projections with Type field
// The bug was about extracting a record with a Type field and a definition
// using forall over that record type.
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.

#include <rocq_bug_4616.h>

int main() {
  // Compilation check only - the definitions are type-level
  return 0;
}
