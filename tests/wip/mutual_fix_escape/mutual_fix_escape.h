#ifndef INCLUDED_MUTUAL_FIX_ESCAPE
#define INCLUDED_MUTUAL_FIX_ESCAPE

#include <functional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct MutualFixEscape {
  /// Mutual fixpoint using fix...with...for syntax, then return
  /// both functions through a pair.
  __attribute__((pure)) static std::pair<std::function<bool(unsigned int)>,
                                         std::function<bool(unsigned int)>>
  make_even_odd(const unsigned int _x);
  /// test1: even(4) = true, odd(3) = true. 1+1=2.
  static inline const unsigned int test1 = []() {
    return []() -> unsigned int {
      auto _cs = make_even_odd(0u);
      const std::function<bool(unsigned int)> &ev = _cs.first;
      const std::function<bool(unsigned int)> &od = _cs.second;
      return ([&]() -> unsigned int {
        if (ev(4u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() + [&]() -> unsigned int {
        if (od(3u)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
  /// test2: even(5) = false, odd(6) = false. 0+0=0.
  static inline const unsigned int test2 = []() {
    return []() -> unsigned int {
      auto _cs = make_even_odd(0u);
      const std::function<bool(unsigned int)> &ev = _cs.first;
      const std::function<bool(unsigned int)> &od = _cs.second;
      return ([&]() -> unsigned int {
        if (ev(5u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() + [&]() -> unsigned int {
        if (od(6u)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
  /// A mutual fixpoint that captures a parameter base.
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>,
                              std::function<unsigned int(unsigned int)>>
  make_count_pair(const unsigned int base);
  /// test3: count_even(0) = base = 10. count_odd(0) = 20.
  /// count_even(3) = 1+count_odd(2) = 1+(1+count_even(1))
  /// = 1+(1+(1+count_odd(0))) = 1+1+1+20 = 23.
  /// Total = 10 + 23 = 33.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_count_pair(10u);
    const std::function<unsigned int(unsigned int)> &ce = _cs.first;
    const std::function<unsigned int(unsigned int)> &_x = _cs.second;
    return (ce(0u) + ce(3u));
  }();
  /// test4: with noise. count_odd(1) = 1+count_even(0) = 1+5 = 6.
  static inline const unsigned int test4 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = make_count_pair(5u);
    return p.second(1u);
  }();
};

#endif // INCLUDED_MUTUAL_FIX_ESCAPE
