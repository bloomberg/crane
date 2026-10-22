#include "loopify_mutual_void.h"

/// Mutual recursion between functions returning nothing.
///
/// A tail call of odd_void is generated as its statement and a return,
/// odd_void(m); return;, which Loopify did not continue in: it ran the
/// partner's body in a lambda, declared a machine with a void _result
/// and called an adopted entry it never defined, and the C++ did not
/// compile.  The call now continues in the partner's body, every path of
/// which ends in a return, and the group is a tail loop.
void LoopifyMutualVoid::even_void(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _inl_n = m;
      if (_inl_n <= 0) {
        return;
      } else {
        uint64_t _inl_m = _inl_n - 1;
        _loop_n = _inl_m;
      }
    }
  }
  return;
}

void LoopifyMutualVoid::odd_void(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _inl_n = m;
      if (_inl_n <= 0) {
        return;
      } else {
        uint64_t _inl_m = _inl_n - 1;
        _loop_n = _inl_m;
      }
    }
  }
  return;
}
