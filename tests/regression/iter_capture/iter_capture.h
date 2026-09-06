#ifndef INCLUDED_ITER_CAPTURE
#define INCLUDED_ITER_CAPTURE

#include <type_traits>
#include <utility>

struct IterCapture {
  static inline const uint64_t run = []() {
    return []() {
      uint64_t acc_ = UINT64_C(100);
      return [](uint64_t _crane_n, auto _crane_f, auto _crane_seed) {
        std::decay_t<decltype(_crane_f(std::move(_crane_seed)))> _crane_acc =
            std::move(_crane_seed);
        for (uint64_t _crane_i = 0; _crane_i < _crane_n; _crane_i++) {
          _crane_acc = _crane_f(std::move(_crane_acc));
        }
        return _crane_acc;
      }(
                 UINT64_C(3), [=](uint64_t x) mutable { return (x + acc_); },
                 UINT64_C(0));
    }();
  }();
};

#endif // INCLUDED_ITER_CAPTURE
