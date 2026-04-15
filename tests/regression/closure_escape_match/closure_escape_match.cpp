#include <closure_escape_match.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Return a closure wrapped in option — prevents uncurrying.
/// The closure captures a pattern variable hd (a shared_ptr),
/// which is an inlined _args.d_a0 inside the std::visit callback.
__attribute__((pure)) std::optional<
    std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>
ClosureEscapeMatch::make_prepender_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>> &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>::Mynil>(
          l->v())) {
    return std::optional<
        std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
            std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>();
  } else {
    const auto &_m = *std::get_if<typename ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>::Mycons>(
        &l->v());
    return std::make_optional<
        std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
            std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>(
        [=](const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>
                &x) mutable { return app<unsigned int>(_m.d_a0, x); });
  }
}

/// Return a closure in a pair — prevents uncurrying.
/// Captures pattern variables x and xs.
__attribute__((pure)) std::optional<
    std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>
ClosureEscapeMatch::make_pair_fn_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &l) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(l->v())) {
    return std::optional<
        std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>();
  } else {
    const auto &_m =
        *std::get_if<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
            &l->v());
    return std::make_optional<
        std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>(
        [=](const std::monostate) mutable {
          return std::make_pair(_m.d_a0, length<unsigned int>(_m.d_a1));
        });
  }
}

/// Nested matches with closures returned in option.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ClosureEscapeMatch::nested_closure_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &a,
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &b) {
  if (std::holds_alternative<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(a->v())) {
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(b->v())) {
      return std::optional<std::function<unsigned int(unsigned int)>>();
    } else {
      const auto &_m0 = *std::get_if<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(&b->v());
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int n) mutable { return (_m0.d_a0 + n); });
    }
  } else {
    const auto &_m =
        *std::get_if<typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(
            &a->v());
    if (std::holds_alternative<
            typename ClosureEscapeMatch::mylist<unsigned int>::Mynil>(b->v())) {
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int n) mutable { return (_m.d_a0 + n); });
    } else {
      const auto &_m0 = *std::get_if<
          typename ClosureEscapeMatch::mylist<unsigned int>::Mycons>(&b->v());
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int n) mutable {
            return ((_m.d_a0 + _m0.d_a0) + n);
          });
    }
  }
}

/// Closure stored in a product, capturing shared_ptr pattern variable.
__attribute__((pure)) std::pair<
    unsigned int,
    std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>
ClosureEscapeMatch::closure_in_pair(
    const std::shared_ptr<ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>> &l) {
  if (std::holds_alternative<typename ClosureEscapeMatch::mylist<
          std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>::Mynil>(
          l->v())) {
    return std::make_pair(
        0u, [](std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> x) {
          return x;
        });
  } else {
    const auto &_m = *std::get_if<typename ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>::Mycons>(
        &l->v());
    return std::make_pair(
        length<unsigned int>(_m.d_a0),
        [=](const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>
                &x) mutable { return app<unsigned int>(_m.d_a0, x); });
  }
}
