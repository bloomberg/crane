// Tail-recursive local fixpoints are loops by default: ten million steps
// would overflow the stack as recursion at -O0.
#include "local_tail_loop_default.h"

#include <cassert>

int main() {
  assert(LocalTailLoopDefault::sum_to(10000000) == 50000005000000ULL);
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  auto r = LocalTailLoopDefault::rev_map([](uint64_t x) { return x * 10; }, l);
  const auto &[h, t] = std::get<List<uint64_t>::Cons>(r.v());
  assert(h == 20);
  return 0;
}
