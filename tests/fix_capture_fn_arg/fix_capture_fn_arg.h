#ifndef INCLUDED_FIX_CAPTURE_FN_ARG
#define INCLUDED_FIX_CAPTURE_FN_ARG

#include <functional>
#include <type_traits>
#include <utility>

struct FixCaptureFnArg {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  make_transform(F0 &&f, uint64_t base) {
    auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return f(base);
      } else {
        uint64_t x_ = x - 1;
        return (_self_go(_self_go, x_) + 1);
      }
    };
    auto go = [=](uint64_t x) mutable -> uint64_t {
      return go_impl(go_impl, x);
    };
    return std::make_pair(f(base), go);
  }

  static inline const uint64_t test1 = []() -> uint64_t {
    auto [n, g] = make_transform([](uint64_t x) { return (x * UINT64_C(2)); },
                                 UINT64_C(5));
    return (n + g(UINT64_C(3)));
  }();
  static inline const uint64_t test2 = []() -> uint64_t {
    auto [n, g] =
        make_transform([](uint64_t x) { return (x + 1); }, UINT64_C(10));
    return (n + g(UINT64_C(5)));
  }();
};

#endif // INCLUDED_FIX_CAPTURE_FN_ARG
