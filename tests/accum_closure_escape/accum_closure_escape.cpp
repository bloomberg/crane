#include "accum_closure_escape.h"

AccumClosureEscape::mylist<std::function<uint64_t(uint64_t)>>
AccumClosureEscape::build_adders(
    const AccumClosureEscape::mylist<uint64_t> &l,
    AccumClosureEscape::mylist<std::function<uint64_t(uint64_t)>> acc) {
  if (std::holds_alternative<
          typename AccumClosureEscape::mylist<uint64_t>::Mynil>(l.v())) {
    return acc;
  } else {
    const auto &[a0, a1] =
        std::get<typename AccumClosureEscape::mylist<uint64_t>::Mycons>(l.v());
    const AccumClosureEscape::mylist<uint64_t> &a1_value = *a1;
    return build_adders(
        a1_value,
        mylist<std::function<uint64_t(uint64_t)>>::mycons(
            [=](uint64_t x) mutable { return (a0 + x); }, std::move(acc)));
  }
}

uint64_t AccumClosureEscape::apply_first(
    const AccumClosureEscape::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return a0(x);
  }
}

uint64_t AccumClosureEscape::apply_all_sum(
    const AccumClosureEscape::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename AccumClosureEscape::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename AccumClosureEscape::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return (a0(x) + apply_all_sum(*a1, x));
  }
}
