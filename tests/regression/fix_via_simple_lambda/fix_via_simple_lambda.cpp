#include <fix_via_simple_lambda.h>

/// Two local fixpoints both capture a let-binding base via &.
/// They are combined in a simple lambda fun x => ... which captures
/// them by = (since simple lambdas use value capture).
///
/// BUG HYPOTHESIS: Copying a std::function that wraps a & lambda
/// does NOT fix the dangling references. The = capture on the outer
/// lambda copies the std::function objects, but the internal &
/// closures still reference the destroyed stack variable base.
///
/// This is a different escape mechanism from existing tests:
/// the fixpoints don't escape directly through a constructor —
/// they escape INDIRECTLY by being captured in a simple lambda
/// that is then stored in Some.
std::optional<std::function<unsigned int(unsigned int)>>
FixViaSimpleLambda::make_combined(const unsigned int &n) {
  unsigned int base = (n * 2u);
  auto double_add_impl = [=](auto &_self_double_add,
                             unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (2u + _self_double_add(_self_double_add, x_));
    }
  };
  auto double_add = [=](unsigned int x) mutable -> unsigned int {
    return double_add_impl(double_add_impl, x);
  };
  auto triple_add_impl = [=](auto &_self_triple_add,
                             unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (3u + _self_triple_add(_self_triple_add, x_));
    }
  };
  auto triple_add = [=](unsigned int x) mutable -> unsigned int {
    return triple_add_impl(triple_add_impl, x);
  };
  return std::make_optional<std::function<unsigned int(unsigned int)>>(
      [=](const unsigned int &x) mutable {
        return (double_add(x) + triple_add(x));
      });
}
