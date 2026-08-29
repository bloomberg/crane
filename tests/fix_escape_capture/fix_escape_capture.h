#ifndef INCLUDED_FIX_ESCAPE_CAPTURE
#define INCLUDED_FIX_ESCAPE_CAPTURE

#include <functional>
#include <utility>

struct FixEscapeCapture {
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  make_pair_fn(uint64_t base);
  static inline const uint64_t test_pair = []() -> uint64_t {
    auto [_x, f] = make_pair_fn(UINT64_C(5));
    return f(UINT64_C(3));
  }();
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  make_pair_fn2(uint64_t base);

  static inline const uint64_t test_pair2 = []() -> uint64_t {
    auto [n, f] = make_pair_fn2(UINT64_C(5));
    return (n + f(UINT64_C(3)));
  }();
};

#endif // INCLUDED_FIX_ESCAPE_CAPTURE
