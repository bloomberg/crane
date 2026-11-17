#include "loopify_mutual_countdown.h"

/// Loopification handles many self-recursive functions, but this probes a
/// mutually recursive countdown.  The Rocq computation is total and uses only
/// bounded numeric values in the C++ test.  With Set Crane Loopify., Crane
/// still emits even_countdown and odd_countdown as ordinary mutually
/// recursive C++ calls instead of a loop, so a deep countdown overflows the C++
/// stack.
bool LoopifyMutualCountdown::even_countdown(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (n_ <= 0) {
        return false;
      } else {
        uint64_t n_0 = n_ - 1;
        _loop_n = n_0;
      }
    }
  }
}

bool LoopifyMutualCountdown::odd_countdown(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return false;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (n_ <= 0) {
        return true;
      } else {
        uint64_t n_0 = n_ - 1;
        _loop_n = n_0;
      }
    }
  }
}
