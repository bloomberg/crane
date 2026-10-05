#include "closure_copy_shares.h"

/// A closure is a shared, immutable value: copying one copies a pointer.
/// The closures below capture a list and other closures, so a copy that
/// cloned its captures would allocate.
uint64_t ClosureCopyShares::sum(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// Captures a list.
uint64_t ClosureCopyShares::adder(const List<uint64_t> &l, uint64_t x) {
  return (sum(l) + x);
}
