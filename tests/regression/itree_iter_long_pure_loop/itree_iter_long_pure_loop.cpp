#include "itree_iter_long_pure_loop.h"

std::shared_ptr<ITree<Sum<uint64_t, uint64_t>>>
ItreeIterLongPureLoop::step(uint64_t n) {
  if (n <= 0) {
    return itree_ret(Sum<uint64_t, uint64_t>::inr(UINT64_C(0)));
  } else {
    uint64_t k = n - 1;
    return itree_ret(Sum<uint64_t, uint64_t>::inl(k));
  }
}

std::shared_ptr<ITree<uint64_t>> ItreeIterLongPureLoop::count_down(uint64_t n) {
  return itree_iter(step, n);
}

std::shared_ptr<ITree<uint64_t>> ItreeIterLongPureLoop::after_taus(uint64_t n) {
  return itree_bind(count_down(n),
                    [](uint64_t r) { return itree_ret((r + 1)); });
}
