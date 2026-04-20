#include <fix_pair_two_closures.h>

#include <functional>
#include <type_traits>
#include <utility>

/// Two local fixpoints escape through a pair.
///
/// BUG: Both f and g use & capture. They capture a, b,
/// and each other's std::function variables. All captured references
/// dangle after make_ops returns.
__attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                std::function<unsigned int(unsigned int)>>
FixPairTwoClosures::make_ops(const unsigned int a, const unsigned int b) {
  std::function<unsigned int(unsigned int)> f;
  f = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return a;
    } else {
      unsigned int x_ = x - 1;
      return (f(x_) + 1);
    }
  };
  std::function<unsigned int(unsigned int)> g;
  g = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return b;
    } else {
      unsigned int x_ = x - 1;
      return (g(x_) + 1);
    }
  };
  return std::make_pair(f, g);
}
