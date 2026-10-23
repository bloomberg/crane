#include <boxed_element_drain.h>
#include <cassert>
#include <cstdint>

using M = BoxedElementDrain;

int main() {
  assert(M::sample_total == 14);
  assert(M::total(M::spine(UINT64_C(10))) == 11);
  // A spine deep enough that destroying it by recursion would exhaust the
  // stack, built here by a loop; the drain takes it apart iteratively.
  {
    M::rose deep = M::rose::node(UINT64_C(1), crane::list<crane::box<M::rose>>{});
    for (int i = 0; i < 200000; ++i)
      deep = M::rose::node(UINT64_C(1), crane::cons(std::move(deep), crane::list<crane::box<M::rose>>{}));
  }
  return 0;
}
