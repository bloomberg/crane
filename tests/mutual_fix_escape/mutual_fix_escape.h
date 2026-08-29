#ifndef INCLUDED_MUTUAL_FIX_ESCAPE
#define INCLUDED_MUTUAL_FIX_ESCAPE

#include <functional>
#include <utility>

struct MutualFixEscape {
  static std::pair<std::function<bool(uint64_t)>, std::function<bool(uint64_t)>>
  make_even_odd(uint64_t _x);
  static inline const uint64_t test1 = []() {
    return []() -> uint64_t {
      auto [ev, od] = make_even_odd(UINT64_C(0));
      return ((ev(UINT64_C(4)) ? UINT64_C(1) : UINT64_C(0)) +
              (od(UINT64_C(3)) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  static inline const uint64_t test2 = []() {
    return []() -> uint64_t {
      auto [ev, od] = make_even_odd(UINT64_C(0));
      return ((ev(UINT64_C(5)) ? UINT64_C(1) : UINT64_C(0)) +
              (od(UINT64_C(6)) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_count_pair(uint64_t base);
  static inline const uint64_t test3 = []() -> uint64_t {
    auto [ce, _x] = make_count_pair(UINT64_C(10));
    return (ce(UINT64_C(0)) + ce(UINT64_C(3)));
  }();
  static inline const uint64_t test4 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = make_count_pair(UINT64_C(5));
    return std::move(p).second(UINT64_C(1));
  }();
};

#endif // INCLUDED_MUTUAL_FIX_ESCAPE
