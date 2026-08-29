#include "closure_escape_match.h"

std::optional<std::function<
    ClosureEscapeMatch::mylist<uint64_t>(ClosureEscapeMatch::mylist<uint64_t>)>>
ClosureEscapeMatch::make_prepender_opt(
    const ClosureEscapeMatch::mylist<ClosureEscapeMatch::mylist<uint64_t>> &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          ClosureEscapeMatch::mylist<uint64_t>>::Mynil>(l.v())) {
    return std::optional<std::function<ClosureEscapeMatch::mylist<uint64_t>(
        ClosureEscapeMatch::mylist<uint64_t>)>>();
  } else {
    const auto &[a0, a1] = std::get<typename ClosureEscapeMatch::mylist<
        ClosureEscapeMatch::mylist<uint64_t>>::Mycons>(l.v());
    return std::make_optional<std::function<ClosureEscapeMatch::mylist<
        uint64_t>(ClosureEscapeMatch::mylist<uint64_t>)>>(
        [=](const ClosureEscapeMatch::mylist<uint64_t> &x) mutable {
          return app<uint64_t>(a0, x);
        });
  }
}

std::optional<std::function<std::pair<uint64_t, uint64_t>(std::monostate)>>
ClosureEscapeMatch::make_pair_fn_opt(
    const ClosureEscapeMatch::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<uint64_t>::Mynil>(l.v())) {
    return std::optional<
        std::function<std::pair<uint64_t, uint64_t>(std::monostate)>>();
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureEscapeMatch::mylist<uint64_t>::Mycons>(l.v());
    const ClosureEscapeMatch::mylist<uint64_t> &a1_value = *a1;
    return std::make_optional<
        std::function<std::pair<uint64_t, uint64_t>(std::monostate)>>(
        [=](std::monostate) mutable {
          return std::make_pair(a0, length<uint64_t>(a1_value));
        });
  }
}

std::optional<std::function<uint64_t(uint64_t)>>
ClosureEscapeMatch::nested_closure_opt(
    const ClosureEscapeMatch::mylist<uint64_t> &a,
    const ClosureEscapeMatch::mylist<uint64_t> &b) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<uint64_t>::Mynil>(a.v())) {
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<uint64_t>::Mynil>(b.v())) {
      return std::optional<std::function<uint64_t(uint64_t)>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename ClosureEscapeMatch::mylist<uint64_t>::Mycons>(
              b.v());
      return std::make_optional<std::function<uint64_t(uint64_t)>>(
          [=](uint64_t n) mutable { return (a00 + n); });
    }
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureEscapeMatch::mylist<uint64_t>::Mycons>(a.v());
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<uint64_t>::Mynil>(b.v())) {
      return std::make_optional<std::function<uint64_t(uint64_t)>>(
          [=](uint64_t n) mutable { return (a0 + n); });
    } else {
      const auto &[a00, a10] =
          std::get<typename ClosureEscapeMatch::mylist<uint64_t>::Mycons>(
              b.v());
      return std::make_optional<std::function<uint64_t(uint64_t)>>(
          [=](uint64_t n) mutable { return ((a0 + a00) + n); });
    }
  }
}

std::pair<uint64_t, std::function<ClosureEscapeMatch::mylist<uint64_t>(
                        ClosureEscapeMatch::mylist<uint64_t>)>>
ClosureEscapeMatch::closure_in_pair(
    const ClosureEscapeMatch::mylist<ClosureEscapeMatch::mylist<uint64_t>> &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          ClosureEscapeMatch::mylist<uint64_t>>::Mynil>(l.v())) {
    return std::make_pair(
        UINT64_C(0), [](ClosureEscapeMatch::mylist<uint64_t> x) { return x; });
  } else {
    const auto &[a0, a1] = std::get<typename ClosureEscapeMatch::mylist<
        ClosureEscapeMatch::mylist<uint64_t>>::Mycons>(l.v());
    return std::make_pair(
        length<uint64_t>(a0),
        [=](const ClosureEscapeMatch::mylist<uint64_t> &x) mutable {
          return app<uint64_t>(a0, x);
        });
  }
}
