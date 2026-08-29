#include "loopify_mutual_countdown.h"

bool LoopifyMutualCountdown::even_countdown(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _inl_n = n_;
      if (_inl_n <= 0) {
        return false;
      } else {
        uint64_t n_ = _inl_n - 1;
        _loop_n = n_;
      }
    }
  }
}

bool LoopifyMutualCountdown::odd_countdown(uint64_t n) {
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return false;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _inl_n = n_;
      if (_inl_n <= 0) {
        return true;
      } else {
        uint64_t n_ = _inl_n - 1;
        _loop_n = n_;
      }
    }
  }
}
