#ifndef INCLUDED_MUTUAL_FIX_ESCAPE
#define INCLUDED_MUTUAL_FIX_ESCAPE

#include <functional>
#include <utility>

struct MutualFixEscape {
  /// Mutual fixpoint using fix...with...for syntax, then return
  /// both functions through a pair.
  static std::pair<std::function<bool(uint64_t)>, std::function<bool(uint64_t)>>
  make_even_odd(uint64_t _x);
  /// test1: even(4) = true, odd(3) = true. 1+1=2.
  static inline const uint64_t test1 = []() {
    return []() -> uint64_t {
      auto _cs = make_even_odd(UINT64_C(0));
      const std::function<bool(uint64_t)> &ev = _cs.first;
      const std::function<bool(uint64_t)> &od = _cs.second;
      return ((ev(UINT64_C(4)) ? UINT64_C(1) : UINT64_C(0)) +
              (od(UINT64_C(3)) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  /// test2: even(5) = false, odd(6) = false. 0+0=0.
  static inline const uint64_t test2 = []() {
    return []() -> uint64_t {
      auto _cs = make_even_odd(UINT64_C(0));
      const std::function<bool(uint64_t)> &ev = _cs.first;
      const std::function<bool(uint64_t)> &od = _cs.second;
      return ((ev(UINT64_C(5)) ? UINT64_C(1) : UINT64_C(0)) +
              (od(UINT64_C(6)) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  /// A mutual fixpoint that captures a parameter base.
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_count_pair(uint64_t base);
  /// test3: count_even(0) = base = 10. count_odd(0) = 20.
  /// count_even(3) = 1+count_odd(2) = 1+(1+count_even(1))
  /// = 1+(1+(1+count_odd(0))) = 1+1+1+20 = 23.
  /// Total = 10 + 23 = 33.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_count_pair(UINT64_C(10));
    const std::function<uint64_t(uint64_t)> &ce = _cs.first;
    const std::function<uint64_t(uint64_t)> &_x = _cs.second;
    return (ce(UINT64_C(0)) + ce(UINT64_C(3)));
  }();
  /// test4: with noise. count_odd(1) = 1+count_even(0) = 1+5 = 6.
  static inline const uint64_t test4 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = make_count_pair(UINT64_C(5));
    return p.second(UINT64_C(1));
  }();
};

#endif // INCLUDED_MUTUAL_FIX_ESCAPE
