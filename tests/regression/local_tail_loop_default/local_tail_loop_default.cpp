#include "local_tail_loop_default.h"

/// A tail-recursive local fixpoint becomes a loop without Crane Loopify:
/// its call depth is bounded however long the input, and it is an ordinary
/// lambda rather than a self-applying one.
uint64_t LocalTailLoopDefault::sum_to(uint64_t n) {
  auto go = [](uint64_t k, uint64_t acc) -> uint64_t {
    uint64_t _loop_acc = std::move(acc);
    uint64_t _loop_k = std::move(k);
    while (true) {
      if (_loop_k <= 0) {
        return _loop_acc;
      } else {
        uint64_t k_ = _loop_k - 1;
        uint64_t _next_k = k_;
        _loop_acc = (_loop_acc + _loop_k);
        _loop_k = _next_k;
      }
    }
  };
  return go(n, UINT64_C(0));
}
