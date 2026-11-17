// A callback that is only called keeps its concrete type through a local
// fixpoint and through a desugared bind: it is passed by reference and never
// copied into a crane::fn.
#include "callback_stays_concrete.h"

#include <cassert>

struct Counting {
  static inline int copies = 0;
  uint64_t k;
  explicit Counting(uint64_t k) : k(k) {}
  Counting(const Counting &o) : k(o.k) { ++copies; }
  uint64_t operator()(uint64_t x) const { return x * k; }
};

int main() {
  using M = CallbackStaysConcrete;
  auto xs = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  Counting f(10);
  Counting::copies = 0;
  assert(M::better_sum(f, xs) == 30);
  assert(M::sum_map_acc(f, xs, 0) == 30);
  assert(M::apply_io(f, 4) == 40);
  assert(Counting::copies == 0);
  return 0;
}
