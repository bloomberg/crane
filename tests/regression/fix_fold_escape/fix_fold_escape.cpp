#include "fix_fold_escape.h"

/// Collect fixpoint closures by folding over a list of nats.
/// Each iteration creates a new fixpoint adder that captures the
/// current element n from the fold callback's parameter.
///
/// BUG HYPOTHESIS: The callback lambda's parameter n lives on the
/// callback's stack frame. The fixpoint adder captures n by &.
/// The callback returns cons adder acc, storing the closure.
/// After the callback returns, n is destroyed. Later iterations and
/// the final result contain dangling closures.
List<std::function<uint64_t(uint64_t)>>
FixFoldEscape::collect_adders(const List<uint64_t> &l) {
  return fold_left(
      [](List<std::function<uint64_t(uint64_t)>> acc, uint64_t n) {
        auto adder_impl = [=](auto &_self_adder,
                              uint64_t x) mutable -> uint64_t {
          if (x <= 0) {
            return n;
          } else {
            uint64_t x_ = x - 1;
            return (_self_adder(_self_adder, x_) + 1);
          }
        };
        auto adder = [=](uint64_t x) mutable -> uint64_t {
          return adder_impl(adder_impl, x);
        };
        return List<std::function<uint64_t(uint64_t)>>::cons(adder, acc);
      },
      List<std::function<uint64_t(uint64_t)>>::nil(), l);
}

uint64_t
FixFoldEscape::apply_head(const List<std::function<uint64_t(uint64_t)>> &l,
                          uint64_t x) {
  if (std::holds_alternative<
          typename List<std::function<uint64_t(uint64_t)>>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::function<uint64_t(uint64_t)>>::Cons>(l.v());
    return a0(x);
  }
}

uint64_t
FixFoldEscape::sum_apply(const List<std::function<uint64_t(uint64_t)>> &l,
                         uint64_t x) {
  if (std::holds_alternative<
          typename List<std::function<uint64_t(uint64_t)>>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::function<uint64_t(uint64_t)>>::Cons>(l.v());
    return (a0(x) + sum_apply(*a1, x));
  }
}
