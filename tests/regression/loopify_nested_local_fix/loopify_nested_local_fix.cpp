#include "loopify_nested_local_fix.h"

uint64_t LoopifyNestedLocalFix::count(const List<uint64_t> &ns) {
  {
    const List<uint64_t> &_lc1_ms = ns;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<uint64_t> *_lc1_loop_ms = &_lc1_ms;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_ms->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_ms->v());
        auto inner = [](uint64_t k, uint64_t a) -> uint64_t {
          uint64_t _loop_a = a;
          uint64_t _loop_k = k;
          while (true) {
            if (_loop_k <= 0) {
              return _loop_a;
            } else {
              uint64_t k_ = _loop_k - 1;
              _loop_a = (_loop_a + 1);
              _loop_k = k_;
            }
          }
        };
        _lc1_loop_acc = inner(a0, _lc1_loop_acc);
        _lc1_loop_ms = crane_raw(a1);
      }
    }
  }
}
