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
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename HofClosureEscape::tree::Node>(t->v());
    if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
            d_a0->v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename HofClosureEscape::tree::Node>(d_a0->v());
      if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
              d_a2->v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename HofClosureEscape::tree::Node>(d_a2->v());
        return (((d_a10 + d_a11) + d_a1) + x);
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
