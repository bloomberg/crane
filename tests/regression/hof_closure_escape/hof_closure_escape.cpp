#include "hof_closure_escape.h"

unsigned int HofClosureEscape::sum_values(const HofClosureEscape::tree &t,
                                          unsigned int x) {
  if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename HofClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename HofClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename HofClosureEscape::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// BUG: The partial application sum_values t creates a & lambda.
/// Even though wrap_some just passes f through to Some,
/// the & lambda was created in hof_escape's stack frame.
/// When hof_escape returns, captured t is destroyed.
std::optional<std::function<unsigned int(unsigned int)>>
HofClosureEscape::hof_escape(const HofClosureEscape::tree &t) {
  return wrap_some([=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  });
}

unsigned int HofClosureEscape::apply_option(
    const std::optional<std::function<unsigned int(unsigned int)>> &o,
    unsigned int x) {
  if (o.has_value()) {
    const std::function<unsigned int(unsigned int)> &f = *o;
    return f(x);
  } else {
    return x;
  }
}
