#include "fix_partial_app_escape.h"

uint64_t FixPartialAppEscape::count_bits(uint64_t _x0) {
  return []() {
    auto go_impl = [](auto &_self_go, uint64_t depth, uint64_t n) -> uint64_t {
      if (depth <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t d = depth - 1;
        if (n <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t _x = n - 1;
          return (_self_go(_self_go, d, (UINT64_C(2) ? n / UINT64_C(2) : 0)) +
                  1);
        }
      }
    };
    auto go = [=](uint64_t depth, uint64_t n) mutable -> uint64_t {
      return go_impl(go_impl, depth, n);
    };
    return [=](uint64_t _pa0) mutable { return go(UINT64_C(32), _pa0); };
  }()(_x0);
}
