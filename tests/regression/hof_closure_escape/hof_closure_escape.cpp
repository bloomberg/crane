#include "hof_closure_escape.h"

uint64_t HofClosureEscape::sum_values(const HofClosureEscape::tree &t,
                                      uint64_t x) {
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
std::optional<std::function<uint64_t(uint64_t)>>
HofClosureEscape::hof_escape(const HofClosureEscape::tree &t) {
  return wrap_some(
      [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); });
}

uint64_t HofClosureEscape::apply_option(
    const std::optional<std::function<uint64_t(uint64_t)>> &o, uint64_t x) {
  if (o.has_value()) {
    const std::function<uint64_t(uint64_t)> &f = *o;
    return f(x);
  } else {
    return x;
  }
}
