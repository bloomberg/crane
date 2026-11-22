#include "deque_fold_fix_init.h"

uint64_t DequeFoldFixInit::compose_all(const std::deque<uint64_t> &l,
                                       const std::deque<uint64_t> &base,
                                       uint64_t x0_) {
  return [](auto _f, const auto &_l, auto _a) {
    for (const auto &_x : _l) _a = _f(_a, _x);
    return _a;
  }(
      [](crane::fn<uint64_t(uint64_t)> acc, uint64_t k) {
        return [=, acc = std::move(acc)](uint64_t x) { return (acc(x) + k); };
      },
      l,
      [&]() {
        auto go =
            [](std::deque<uint64_t> m, crane::fn<uint64_t(uint64_t)> acc,
               uint64_t x0_0)
                 -> uint64_t {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              crane::fn<uint64_t(uint64_t)> _loop_acc = std::move(acc);
              std::deque<uint64_t> _loop_m = std::move(m);
              while (true) {
                if (_loop_m.empty()) {
                  return _loop_acc(x0_0);
                } else {
                  const uint64_t &j = _loop_m.front();
                  std::deque<uint64_t> r =
                      std::deque<uint64_t>(_loop_m.begin() + 1, _loop_m.end());
                  _loop_acc =
                      [=, _loop_acc = std::move(_loop_acc)](uint64_t x) {
                        return (_loop_acc(x) + j);
                      };
                  _loop_m = std::move(r);
                }
              }
            };
        return [=](uint64_t _pa0) {
          return go(base, [](uint64_t x) { return x; }, _pa0);
        };
      }())(x0_);
}

std::deque<uint64_t>
DequeFoldFixInit::with_let(bool b, const std::deque<uint64_t> &x0_) {
  return [](auto _f, const auto &_l, auto _a) {
    for (const auto &_x : _l) _a = _f(_a, _x);
    return _a;
  }(
      [](crane::fn<std::deque<uint64_t>(std::deque<uint64_t>)> acc,
         uint64_t) { return acc; },
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(0), std::deque<uint64_t>{}),
      [&]() {
        bool c = !(b);
        return [=](std::deque<uint64_t> l) -> std::deque<uint64_t> {
          if (c) {
            return [](auto _a0, auto _a1) {
              _a1.push_front(_a0);
              return _a1;
            }(UINT64_C(1), std::move(l));
          } else {
            return l;
          }
        };
      }())(x0_);
}
