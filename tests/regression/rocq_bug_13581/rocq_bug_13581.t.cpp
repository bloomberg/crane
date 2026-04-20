// Rocq bug #13581: complex records with let-bindings in parameters,
// mutual inductives, and mutual coinductives.
// The bug was about handling records/inductives with let-binding parameters
// (like (c:=b) and (T:=T0)) and mutual inductive/coinductive definitions.
//
// Bug status in Crane: NOT REPLICATED. Complex records with let-binding
// parameters and mutual inductives extract and compile correctly.

#include <rocq_bug_13581.h>

int main() {
  // Compilation check - complex record and inductive structures
  return 0;
}
