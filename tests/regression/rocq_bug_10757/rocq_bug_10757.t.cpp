// Rocq bug #10757: extraction of Program Fixpoint with sig type
// and well-founded recursion. The bug was about correctly extracting
// Program Fixpoints that use well-founded recursion and return sig types.
//
// Bug status in Crane: NOT REPLICATED. Program Fixpoint with sig type
// and well-founded recursion extracts and compiles correctly.

#include <rocq_bug_10757.h>

int main() {
  // Compilation check only - iterate is parameterized by abstract types
  return 0;
}
