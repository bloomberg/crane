#include <accum_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Fold-left that builds a closure from each element.
///
/// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
/// h from the pattern match. These are simple lambdas, so they
/// should capture by =.
__attribute__((pure))
AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
AccumClosureEscape::build_adders(
    const AccumClosureEscape::mylist<unsigned int> &l,
    AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>> acc) {
  if (std::holds_alternative<
          typename AccumClosureEscape::mylist<unsigned int>::Mynil>(l.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename AccumClosureEscape::mylist<unsigned int>::Mycons>(
            l.v());
    AccumClosureEscape::mylist<unsigned int> d_a1_value =
        clone_as_value<AccumClosureEscape::mylist<unsigned int>>(d_a1);
    return build_adders(
        d_a1_value,
        mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](const unsigned int &x) mutable { return (d_a0 + x); }, acc));
  }
}

/// Apply first closure from the list.
__attribute__((pure)) unsigned int AccumClosureEscape::apply_first(
    const AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int &x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return d_a0(x);
  }
}

/// Apply all closures and sum.
__attribute__((pure)) unsigned int AccumClosureEscape::apply_all_sum(
    const AccumClosureEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int &x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return (d_a0(x) + apply_all_sum(*(d_a1), x));
  }
}
