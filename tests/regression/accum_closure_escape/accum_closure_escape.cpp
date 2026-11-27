#include "accum_closure_escape.h"

/// Fold-left that builds a closure from each element.
///
/// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
/// h from the pattern match. These are simple lambdas, so they
/// should capture by =.
AccumClosureEscape::mylist<crane::fn<uint64_t(uint64_t)>>
AccumClosureEscape::build_adders(
    const AccumClosureEscape::mylist<uint64_t> &l,
    AccumClosureEscape::mylist<crane::fn<uint64_t(uint64_t)>> acc) {
  if (std::holds_alternative<
          typename AccumClosureEscape::mylist<uint64_t>::Mynil>(l.v())) {
    return acc;
  } else {
    const auto &[a0, a1] =
        std::get<typename AccumClosureEscape::mylist<uint64_t>::Mycons>(l.v());
    const AccumClosureEscape::mylist<uint64_t> &a1_value = *a1;
    return build_adders(a1_value, mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
                                      [=](uint64_t x) { return (a0 + x); },
                                      std::move(acc)));
  }
}

/// Apply first closure from the list.
uint64_t AccumClosureEscape::apply_first(
    const AccumClosureEscape::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, _] = std::get<typename AccumClosureEscape::mylist<
        crane::fn<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return a0(x);
  }
}

/// Apply all closures and sum.
uint64_t AccumClosureEscape::apply_all_sum(
    const AccumClosureEscape::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename AccumClosureEscape::mylist<
        crane::fn<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return (a0(x) + apply_all_sum(*a1, x));
  }
}

/// COMPOSE CLOSURES: Each step builds a composed function.
/// This creates closures that capture OTHER closures.
uint64_t AccumClosureEscape::compose_from_list(
    const AccumClosureEscape::mylist<uint64_t> &l,
    const crane::fn<uint64_t(uint64_t)> &acc, uint64_t x0_) {
  if (std::holds_alternative<
          typename AccumClosureEscape::mylist<uint64_t>::Mynil>(l.v())) {
    return acc(x0_);
  } else {
    const auto &[a0, a1] =
        std::get<typename AccumClosureEscape::mylist<uint64_t>::Mycons>(l.v());
    const AccumClosureEscape::mylist<uint64_t> &a1_value = *a1;
    return compose_from_list(
        a1_value,
        [=, acc = acc](uint64_t x) { return acc((a0 + x)); },
        x0_);
  }
}
