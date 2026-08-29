#ifndef INCLUDED_CLOSURE_NESTED_ESCAPE
#define INCLUDED_CLOSURE_NESTED_ESCAPE

#include <functional>
#include <utility>

struct ClosureNestedEscape {
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_pair_fix(uint64_t n);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto [f, g] = make_pair_fix(UINT64_C(5));
    return (f(UINT64_C(3)) + g(UINT64_C(3)));
  }();
  static inline const uint64_t test2 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = make_pair_fix(UINT64_C(7));
    return (p.first(UINT64_C(0)) + p.second(UINT64_C(4)));
  }();
  static inline const uint64_t test3 = []() -> uint64_t {
    auto [_x, g] = make_pair_fix(UINT64_C(3));
    return g(UINT64_C(10));
  }();
};

#endif // INCLUDED_CLOSURE_NESTED_ESCAPE
