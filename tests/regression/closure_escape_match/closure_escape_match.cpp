#include <closure_escape_match.h>

/// Return a closure wrapped in option — prevents uncurrying.
/// The closure captures a pattern variable hd (a shared_ptr),
/// which is an inlined _args.d_a0 inside the std::visit callback.
std::optional<std::function<ClosureEscapeMatch::mylist<unsigned int>(
    ClosureEscapeMatch::mylist<unsigned int>)>>
ClosureEscapeMatch::make_prepender_opt(
    const ClosureEscapeMatch::mylist<ClosureEscapeMatch::mylist<unsigned int>>
        &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          ClosureEscapeMatch::mylist<unsigned int>>::Mynil>(l.v())) {
    return std::optional<std::function<ClosureEscapeMatch::mylist<unsigned int>(
        ClosureEscapeMatch::mylist<unsigned int>)>>();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename ClosureEscapeMatch::mylist<
        ClosureEscapeMatch::mylist<unsigned int>>::Mycons>(l.v());
    return std::make_optional<std::function<ClosureEscapeMatch::mylist<
        unsigned int>(ClosureEscapeMatch::mylist<unsigned int>)>>(
        [=](const ClosureEscapeMatch::mylist<unsigned int> &x) mutable {
          return app<unsigned int>(d_a0, x);
        });
  }
}

/// Return a closure in a pair — prevents uncurrying.
/// Captures pattern variables x and xs.
std::optional<
    std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>
ClosureEscapeMatch::make_pair_fn_opt(
    const ClosureEscapeMatch::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(l.v())) {
    return std::optional<
        std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
            l.v());
    ClosureEscapeMatch::mylist<unsigned int> d_a1_value = *(d_a1);
    return std::make_optional<
        std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>(
        [=](const std::monostate &) mutable {
          return std::make_pair(d_a0, length<unsigned int>(d_a1_value));
        });
  }
}

/// Nested matches with closures returned in option.
std::optional<std::function<unsigned int(unsigned int)>>
ClosureEscapeMatch::nested_closure_opt(
    const ClosureEscapeMatch::mylist<unsigned int> &a,
    const ClosureEscapeMatch::mylist<unsigned int> &b) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(a.v())) {
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(b.v())) {
      return std::optional<std::function<unsigned int(unsigned int)>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
              b.v());
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int &n) mutable { return (d_a00 + n); });
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
            a.v());
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(b.v())) {
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int &n) mutable { return (d_a0 + n); });
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
              b.v());
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int &n) mutable { return ((d_a0 + d_a00) + n); });
    }
  }
}

/// Closure stored in a product, capturing shared_ptr pattern variable.
std::pair<unsigned int, std::function<ClosureEscapeMatch::mylist<unsigned int>(
                            ClosureEscapeMatch::mylist<unsigned int>)>>
ClosureEscapeMatch::closure_in_pair(
    const ClosureEscapeMatch::mylist<ClosureEscapeMatch::mylist<unsigned int>>
        &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          ClosureEscapeMatch::mylist<unsigned int>>::Mynil>(l.v())) {
    return std::make_pair(
        0u, [](ClosureEscapeMatch::mylist<unsigned int> x) { return x; });
  } else {
    const auto &[d_a0, d_a1] = std::get<typename ClosureEscapeMatch::mylist<
        ClosureEscapeMatch::mylist<unsigned int>>::Mycons>(l.v());
    return std::make_pair(
        length<unsigned int>(d_a0),
        [=](const ClosureEscapeMatch::mylist<unsigned int> &x) mutable {
          return app<unsigned int>(d_a0, x);
        });
  }
}
