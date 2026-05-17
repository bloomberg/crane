#include "accum_closure_escape.h"

/// Fold-left that builds a closure from each element.
///
/// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
/// h from the pattern match. These are simple lambdas, so they
/// should capture by =.
AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
AccumClosureEscape::build_adders(
    const AccumClosureEscape::mylist<unsigned int> &l,
    AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>> acc) {
  if (std::holds_alternative<
          typename AccumClosureEscape::mylist<unsigned int>::Mynil>(l.v())) {
    return acc;
  } else {
    const auto &[a0, a1] =
        std::get<typename AccumClosureEscape::mylist<unsigned int>::Mycons>(
            l.v());
    const AccumClosureEscape::mylist<unsigned int> &a1_value = *a1;
    return build_adders(
        a1_value,
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](unsigned int x) mutable { return (a0 + x); }, std::move(acc)));
  }
}

/// Apply first closure from the list.
unsigned int AccumClosureEscape::apply_first(
    const AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    unsigned int x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return a0(x);
  }
}

/// Apply all closures and sum.
unsigned int AccumClosureEscape::apply_all_sum(
    const AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    unsigned int x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return (a0(x) + apply_all_sum(*a1, x));
  }
}
