#include "deque_fold_function_acc.h"

uint64_t DequeFoldFunctionAcc::compose_all(const std::deque<uint64_t> &l,
                                           uint64_t x0_) {
  return [](auto _f, const auto &_l, auto _a) {
    for (const auto &_x : _l) _a = _f(_a, _x);
    return _a;
  }(
      [](crane::fn<uint64_t(uint64_t)> acc, uint64_t k) {
        return [=, acc = std::move(acc)](uint64_t x) { return (acc(x) + k); };
      },
      l,
      [](uint64_t x) { return x; })(x0_);
}
