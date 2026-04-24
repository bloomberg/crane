#include <fix_fold_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Collect fixpoint closures by folding over a list of nats.
/// Each iteration creates a new fixpoint adder that captures the
/// current element n from the fold callback's parameter.
///
/// BUG HYPOTHESIS: The callback lambda's parameter n lives on the
/// callback's stack frame. The fixpoint adder captures n by &.
/// The callback returns cons adder acc, storing the closure.
/// After the callback returns, n is destroyed. Later iterations and
/// the final result contain dangling closures.
__attribute__((pure)) List<std::function<unsigned int(unsigned int)>>
FixFoldEscape::collect_adders(const List<unsigned int> &l) {
  return fold_left(
      [](List<std::function<unsigned int(unsigned int)>> acc, unsigned int n) {
        auto adder =
            std::make_shared<std::function<unsigned int(unsigned int)>>();
        *adder = [=](unsigned int x) mutable -> unsigned int {
          if (x <= 0) {
            return n;
          } else {
            unsigned int x_ = x - 1;
            return ((*adder)(x_) + 1);
          }
        };
        return List<std::function<unsigned int(unsigned int)>>::cons((*adder),
                                                                     acc);
      },
      List<std::function<unsigned int(unsigned int)>>::nil(), l);
}

__attribute__((pure)) unsigned int FixFoldEscape::apply_head(
    const List<std::function<unsigned int(unsigned int)>> &l,
    const unsigned int &x) {
  if (std::holds_alternative<
          typename List<std::function<unsigned int(unsigned int)>>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<std::function<unsigned int(unsigned int)>>::Cons>(l.v());
    return d_a0(x);
  }
}

__attribute__((pure)) unsigned int FixFoldEscape::sum_apply(
    const List<std::function<unsigned int(unsigned int)>> &l,
    const unsigned int &x) {
  if (std::holds_alternative<
          typename List<std::function<unsigned int(unsigned int)>>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<std::function<unsigned int(unsigned int)>>::Cons>(l.v());
    return (d_a0(x) + sum_apply(*(d_a1), x));
  }
}
