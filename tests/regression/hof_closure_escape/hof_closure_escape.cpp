#include <hof_closure_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
HofClosureEscape::sum_values(const std::shared_ptr<HofClosureEscape::tree> &t,
                             const unsigned int x) {
  if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(t->v())) {
    return x;
  } else {
    const auto &_m =
        *std::get_if<typename HofClosureEscape::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
            _sv0->v())) {
      return (_m.d_a1 + x);
    } else {
      const auto &_m0 =
          *std::get_if<typename HofClosureEscape::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m.d_a2;
      if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
              _sv1->v())) {
        return (_m0.d_a1 + x);
      } else {
        const auto &_m1 =
            *std::get_if<typename HofClosureEscape::tree::Node>(&_sv1->v());
        return (((_m0.d_a1 + _m1.d_a1) + _m.d_a1) + x);
      }
    }
  }
}

/// BUG: The partial application sum_values t creates a & lambda.
/// Even though wrap_some just passes f through to Some,
/// the & lambda was created in hof_escape's stack frame.
/// When hof_escape returns, captured t is destroyed.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
HofClosureEscape::hof_escape(std::shared_ptr<HofClosureEscape::tree> t) {
  return wrap_some([=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  });
}

__attribute__((pure)) unsigned int HofClosureEscape::apply_option(
    const std::optional<std::function<unsigned int(unsigned int)>> o,
    const unsigned int x) {
  if (o.has_value()) {
    const std::function<unsigned int(unsigned int)> &f = *o;
    return f(x);
  } else {
    return x;
  }
}
