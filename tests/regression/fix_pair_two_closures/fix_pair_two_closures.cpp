#include <fix_pair_two_closures.h>

/// Two local fixpoints escape through a pair.
///
/// BUG: Both f and g use & capture. They capture a, b,
/// and each other's std::function variables. All captured references
/// dangle after make_ops returns.
std::pair<std::function<unsigned int(unsigned int)>,
          std::function<unsigned int(unsigned int)>>
FixPairTwoClosures::make_ops(unsigned int a, unsigned int b) {
  auto f_impl = [=](auto &_self_f, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return a;
    } else {
      unsigned int x_ = x - 1;
      return (_self_f(_self_f, x_) + 1);
    }
  };
  auto f = [=](unsigned int x) mutable -> unsigned int {
    return f_impl(f_impl, x);
  };
  auto g_impl = [=](auto &_self_g, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return b;
    } else {
      unsigned int x_ = x - 1;
      return (_self_g(_self_g, x_) + 1);
    }
  };
  auto g = [=](unsigned int x) mutable -> unsigned int {
    return g_impl(g_impl, x);
  };
  return std::make_pair(f, g);
}
