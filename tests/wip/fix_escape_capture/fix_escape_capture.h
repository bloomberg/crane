#ifndef INCLUDED_FIX_ESCAPE_CAPTURE
#define INCLUDED_FIX_ESCAPE_CAPTURE

#include <functional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixEscapeCapture {
  /// A local fixpoint that captures a function parameter and is returned
  /// in a pair. The fixpoint's & capture creates a dangling reference
  /// to the captured parameter after the enclosing function returns.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_pair_fn(const unsigned int base);
  /// Invokes the escaped fixpoint — use-after-free if & capture.
  static inline const unsigned int test_pair = []() -> unsigned int {
    auto _cs = make_pair_fn(5u);
    const unsigned int &_x = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return f(3u);
  }();
  /// Same pattern with a non-recursive local fixpoint to isolate the
  /// capture issue from self-reference.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_pair_fn2(const unsigned int base);

  static inline const unsigned int test_pair2 = []() -> unsigned int {
    auto _cs = make_pair_fn2(5u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return (n + f(3u));
  }();
};

#endif // INCLUDED_FIX_ESCAPE_CAPTURE
