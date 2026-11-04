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

  // The eliminator's machine walks the graph, handing each step the tail
  // it stands for.
  List<uint64_t> m = List<uint64_t>::nil();
  uint64_t expected = 7, below = 0;
  for (uint64_t i = 0; i < 2000; ++i) {
    m = List<uint64_t>::cons(i % 3, m);
    expected += i % 3 + 10 * below;
    below = i % 3 + 1;
  }
  auto step = [](uint64_t &x, List<uint64_t> &xs, uint64_t &&r) -> uint64_t {
    const auto *c = std::get_if<List<uint64_t>::Cons>(&xs.v());
    return r + x + 10 * (c ? c->a + 1 : 0);
  };
  assert(M::plain_elim<uint64_t>(7, step, m) == expected);
  return 0;
}
