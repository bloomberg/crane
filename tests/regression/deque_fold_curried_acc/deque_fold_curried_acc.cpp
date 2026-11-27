#include "deque_fold_curried_acc.h"

uint64_t DequeFoldCurriedAcc::g(const std::deque<uint64_t> &l, uint64_t x0_,
                                bool x1_) {
  return [](auto _f, auto _a, const auto &_l) {
    for (auto _it = _l.rbegin(); _it != _l.rend(); ++_it) _a = _f(*_it, _a);
    return _a;
  }(
      [](uint64_t k, crane::fn<uint64_t(uint64_t, bool)> acc) {
        return [=, acc = std::move(acc)](uint64_t x,
                                         bool b) { return acc(x + k, b); };
      },
      crane::fn<uint64_t(uint64_t, bool)>([](uint64_t x, bool b) -> uint64_t {
        if (b) {
          return x;
        } else {
          return UINT64_C(0);
        }
      }),
      l)(x0_, x1_);
}
