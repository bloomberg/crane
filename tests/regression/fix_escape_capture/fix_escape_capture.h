#ifndef INCLUDED_FIX_ESCAPE_CAPTURE
#define INCLUDED_FIX_ESCAPE_CAPTURE

#include <functional>
#include <utility>

struct FixEscapeCapture {
  /// A local fixpoint that captures a function parameter and is returned
  /// in a pair. The fixpoint's & capture creates a dangling reference
  /// to the captured parameter after the enclosing function returns.
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  make_pair_fn(uint64_t base);
  /// Invokes the escaped fixpoint — use-after-free if & capture.
  static inline const uint64_t test_pair = []() -> uint64_t {
    auto _cs = make_pair_fn(UINT64_C(5));
    uint64_t _x = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> f = std::move(_cs.second);
    return f(UINT64_C(3));
  }();
  /// Same pattern with a non-recursive local fixpoint to isolate the
  /// capture issue from self-reference.
  static std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
  make_pair_fn2(uint64_t base);

  static inline const uint64_t test_pair2 = []() -> uint64_t {
    auto _cs = make_pair_fn2(UINT64_C(5));
    uint64_t n = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> f = std::move(_cs.second);
    return (n + f(UINT64_C(3)));
  }();
};

#endif // INCLUDED_FIX_ESCAPE_CAPTURE
