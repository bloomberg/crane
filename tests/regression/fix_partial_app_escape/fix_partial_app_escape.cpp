#include "fix_partial_app_escape.h"

unsigned int FixPartialAppEscape::count_bits(const unsigned int _x0) {
  return []() {
    auto go_impl = [](auto &_self_go, unsigned int depth,
                      unsigned int n) -> unsigned int {
      if (depth <= 0) {
        return 0u;
      } else {
        unsigned int d = depth - 1;
        if (n <= 0) {
          return 0u;
        } else {
          unsigned int _x = n - 1;
          return (_self_go(_self_go, d, (2u ? n / 2u : 0)) + 1);
        }
      }
    };
    auto go = [=](unsigned int depth, unsigned int n) mutable -> unsigned int {
      return go_impl(go_impl, n, depth);
    };
    return [=](unsigned int _pa0) mutable { return go(32u, _pa0); };
  }()(_x0);
}
