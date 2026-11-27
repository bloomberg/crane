#include "deque_fold_function_acc.h"

uint64_t DequeFoldFunctionAcc::compose_all(const std::deque<uint64_t> &l,
                                           uint64_t x0_) {
  return [](auto _f, const auto &_l, auto _a) {
    for (const auto &_x : _l) _a = _f(_a, _x);
    return _a;
  }(
      [](crane::fn<uint64_t(uint64_t)> acc, uint64_t k) {
        return [=, acc = std::move(acc)](uint64_t x) { return acc(x) + k; };
      },
      l,
      crane::fn<uint64_t(uint64_t)>([](uint64_t x) { return x; }))(x0_);
}

/// The same through fold_right, and with a global function as the
/// initial value.
uint64_t DequeFoldFunctionAcc::compose_right(const std::deque<uint64_t> &l,
                                             uint64_t x0_) {
  return [](auto _f, auto _a, const auto &_l) {
    for (auto _it = _l.rbegin(); _it != _l.rend(); ++_it) _a = _f(*_it, _a);
    return _a;
  }(
      [](uint64_t k, crane::fn<uint64_t(uint64_t)> acc) {
        return [=, acc = std::move(acc)](uint64_t x) { return acc(x) * k; };
      },
      crane::fn<uint64_t(uint64_t)>([](uint64_t x) { return x; }),
      l)(x0_);
}

uint64_t DequeFoldFunctionAcc::twice(uint64_t x) { return x + x; }

uint64_t DequeFoldFunctionAcc::compose_glob(const std::deque<uint64_t> &l,
                                            uint64_t x0_) {
  return [](auto _f, const auto &_l, auto _a) {
    for (const auto &_x : _l) _a = _f(_a, _x);
    return _a;
  }(
      [](crane::fn<uint64_t(uint64_t)> acc, uint64_t k) {
        return [=, acc = std::move(acc)](uint64_t x) { return acc(x) + k; };
      },
      l,
      crane::fn<uint64_t(uint64_t)>(twice))(x0_);
}

/// A list of functions built by the mapped map, applied.
std::deque<crane::fn<uint64_t(uint64_t)>>
DequeFoldFunctionAcc::adders(const std::deque<uint64_t> &l) {
  return [](auto _f, const auto &_l) {
    std::deque<crane::fn<uint64_t(uint64_t)>> _r;
    for (const auto &_x : _l) _r.push_back(_f(_x));
    return _r;
  }(
      [](uint64_t k) {
        return [=](uint64_t x) { return x + k; };
      },
      l);
}
