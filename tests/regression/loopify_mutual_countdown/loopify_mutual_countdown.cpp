#include "loopify_mutual_countdown.h"

/// Loopification handles many self-recursive functions, but this probes a
/// mutually recursive countdown.  The Rocq computation is total and uses only
/// bounded numeric values in the C++ test.  With Set Crane Loopify., Crane
/// still emits even_countdown and odd_countdown as ordinary mutually
/// recursive C++ calls instead of a loop, so a deep countdown overflows the C++
/// stack.
bool LoopifyMutualCountdown::even_countdown(const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      _result = true;
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      const unsigned int _inl_n = n_;
      if (_inl_n <= 0) {
        _result = false;
        break;
      } else {
        unsigned int n_ = _inl_n - 1;
        _loop_n = n_;
      }
    }
  }
  return _result;
}

bool LoopifyMutualCountdown::odd_countdown(const unsigned int n) {
  bool _result;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      _result = false;
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      const unsigned int _inl_n = n_;
      if (_inl_n <= 0) {
        _result = true;
        break;
      } else {
        unsigned int n_ = _inl_n - 1;
        _loop_n = n_;
      }
    }
  }
  return _result;
}
