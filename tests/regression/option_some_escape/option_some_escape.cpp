#include "option_some_escape.h"

uint64_t OptionSomeEscape::sum_values(const OptionSomeEscape::tree &t,
                                      uint64_t x) {
  if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename OptionSomeEscape::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(
            _sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename OptionSomeEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename OptionSomeEscape::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in Some (std::make_optional).
/// The & lambda captures parameter t by reference.
/// return_captures_by_value doesn't handle lambdas inside
/// std::make_optional. When the function returns, t is destroyed.
std::optional<std::function<uint64_t(uint64_t)>>
OptionSomeEscape::option_escape(OptionSomeEscape::tree t) {
  return std::make_optional<std::function<uint64_t(uint64_t)>>(
      [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); });
}

uint64_t OptionSomeEscape::apply_option(
    const std::optional<std::function<uint64_t(uint64_t)>> &o, uint64_t x) {
  if (o.has_value()) {
    const std::function<uint64_t(uint64_t)> &f = *o;
    return f(x);
  } else {
    return x;
  }
}
