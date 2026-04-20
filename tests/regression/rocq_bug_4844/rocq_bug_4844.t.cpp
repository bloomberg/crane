// Rocq bug #4844 (and #4824): extraction confusion between unknown and
// dummy types. The Haskell extraction erroneously considered Any and ()
// as convertible. This tests logical parts in sums and boxed values.
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.
// Crane handles the distinction between logical/erased types correctly.

#include <rocq_bug_4844.h>

int main() {
  // Compilation check - the bug was about type confusion in extraction
  return 0;
}
