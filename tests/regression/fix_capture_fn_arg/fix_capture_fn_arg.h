#ifndef INCLUDED_FIX_CAPTURE_FN_ARG
#define INCLUDED_FIX_CAPTURE_FN_ARG

#include <functional>
#include <type_traits>
#include <utility>

struct FixCaptureFnArg {
  /// A local fixpoint captures a FUNCTION argument AND is returned
  /// through a pair (preventing uncurrying).
  ///
  /// BUG: go uses & capture. Both f (a std::function on the
  /// caller's stack) and base are captured by reference.
  /// The fixpoint escapes through the pair — after make_transform
  /// returns, f (the std::function object), base, and the local
  /// go are all destroyed. The returned closure dereferences a
  /// destroyed std::function when it calls f.
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

  /// test1: make_transform(x=>x*2, 5) = (10, go).
  /// go(3) = (5*2) + 3 = 13. Total = 10 + 13 = 23.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_transform([](uint64_t x) { return (x * UINT64_C(2)); },
                              UINT64_C(5));
    const uint64_t &n = _cs.first;
    const std::function<uint64_t(uint64_t)> &g = _cs.second;
    return (n + g(UINT64_C(3)));
  }();
  /// test2: make_transform(S, 10) = (11, go).
  /// go(5) = S(10) + 5 = 16. Total = 11 + 16 = 27.
  static inline const uint64_t test2 = []() -> uint64_t {
    auto _cs = make_transform([](uint64_t x) { return (x + 1); }, UINT64_C(10));
    const uint64_t &n = _cs.first;
    const std::function<uint64_t(uint64_t)> &g = _cs.second;
    return (n + g(UINT64_C(5)));
  }();
};

#endif // INCLUDED_FIX_CAPTURE_FN_ARG
