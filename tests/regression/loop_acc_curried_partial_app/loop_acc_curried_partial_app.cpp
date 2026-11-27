#include "loop_acc_curried_partial_app.h"

bool LoopAccCurriedPartialApp::r(const List<uint64_t> &l) {
  const crane::fn<bool(uint64_t, bool)> &_lc1_acc =
      [](uint64_t n, bool b) { return (b && (n == UINT64_C(0))); };
  uint64_t _lc1_x0_ = UINT64_C(5);
  bool _lc1_x1_ = true;
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  crane::fn<bool(uint64_t, bool)> _lc1_loop_acc = _lc1_acc;
  const List<uint64_t> *_lc1_loop_l0 = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_l0->v())) {
      return _lc1_loop_acc(_lc1_x0_, _lc1_x1_);
    } else {
      const auto &[_, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
      const List<uint64_t> &a1_value = *a1;
      _lc1_loop_acc = [=](uint64_t,
                          bool eta0_) {
        return _lc1_loop_acc(UINT64_C(0), eta0_);
      };
      _lc1_loop_l0 = &a1_value;
    }
  }
}
