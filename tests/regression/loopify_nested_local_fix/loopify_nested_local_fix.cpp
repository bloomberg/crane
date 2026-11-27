#include "loopify_nested_local_fix.h"

uint64_t LoopifyNestedLocalFix::count(const List<uint64_t> &ns) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  const List<uint64_t> *_lc1_loop_ms = &ns;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_ms->v())) {
      return _lc1_loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_ms->v());
      auto inner = [&](uint64_t a) -> uint64_t {
        // Loop replaces the tail recursion: each recursive call updates the
        // loop variables.
        uint64_t _loop_k = a0;
        while (true) {
          if (_loop_k <= 0) {
            return a;
          } else {
            uint64_t k_ = _loop_k - 1;
            a = (a + 1);
            _loop_k = k_;
          }
        }
      };
      _lc1_loop_acc = inner(_lc1_loop_acc);
      _lc1_loop_ms = crane_raw(a1);
    }
  }
}
