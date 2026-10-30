#include <loopify_equations_with_clause.h>

#include <cassert>
#include <cstdint>

using M = LoopifyEquationsWithClause;

int main() {
  assert(M::zeros(List<uint64_t>::nil()) == 0);
  assert(M::plain(List<uint64_t>::nil()) == 0);

  // Deeper than the C++ stack would allow a recursive zeros.
  List<uint64_t> l = List<uint64_t>::nil();
  for (uint64_t i = 0; i < 1000000; ++i) l = List<uint64_t>::cons(i % 3, l);
  assert(M::zeros(l) == 333334);
  assert(M::plain(l) == 999999);
  return 0;
}
