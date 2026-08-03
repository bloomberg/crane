#include <guard_compare_label_collision.h>

// This test is expected to fail to *compile* -- see README.md. The Label-
// keyed `Crane Guard Compare` table injects an ill-typed
// `return Comparison::EQ;` fast path into `Ordered::compare` (which returns
// `Compare<Ordered::T>`, not `Comparison`) purely because it shares the
// trailing label "compare" with the guarded `OK::compare`. If this file
// ever compiles, the Label-keying bug has been fixed.
int main() {
  auto r = OK::compare(Nat::o(), Nat::o());
  return r == Comparison::EQ ? 0 : 1;
}
