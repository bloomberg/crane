#include "local_tail_loop_default.h"

/// A tail-recursive local fixpoint becomes a loop without Crane Loopify:
/// its call depth is bounded however long the input, and it is an ordinary
/// lambda rather than a self-applying one.
uint64_t LocalTailLoopDefault::sum_to(uint64_t n) {
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    uint64_t _lc1_loop_k = _lc1_k;
    while (true) {
      if (_lc1_loop_k <= 0) {
        return _lc1_loop_acc;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        uint64_t _next_k = k_;
        _lc1_loop_acc = (_lc1_loop_acc + _lc1_loop_k);
        _lc1_loop_k = _next_k;
      }
    }
  }
}
