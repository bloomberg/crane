#include <hof_closure_escape.h>

unsigned int HofClosureEscape::sum_values(const HofClosureEscape::tree &t,
                                          unsigned int x) {
  if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename HofClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename HofClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *(d_a2);
      if (std::holds_alternative<typename HofClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename HofClosureEscape::tree::Node>(_sv1.v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// BUG: The partial application sum_values t creates a & lambda.
/// Even though wrap_some just passes f through to Some,
/// the & lambda was created in hof_escape's stack frame.
/// When hof_escape returns, captured t is destroyed.
std::optional<std::function<unsigned int(unsigned int)>>
HofClosureEscape::hof_escape(HofClosureEscape::tree t) {
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
