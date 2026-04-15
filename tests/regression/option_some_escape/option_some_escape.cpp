#include <option_some_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
OptionSomeEscape::sum_values(const std::shared_ptr<OptionSomeEscape::tree> &t,
                             const unsigned int x) {
  if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(t->v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename OptionSomeEscape::tree::Node>(t->v());
    if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(
            d_a0->v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename OptionSomeEscape::tree::Node>(d_a0->v());
      if (std::holds_alternative<typename OptionSomeEscape::tree::Leaf>(
              d_a2->v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename OptionSomeEscape::tree::Node>(d_a2->v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// BUG: Partial application stored in Some (std::make_optional).
/// The & lambda captures parameter t by reference.
/// return_captures_by_value doesn't handle lambdas inside
/// std::make_optional. When the function returns, t is destroyed.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
OptionSomeEscape::option_escape(std::shared_ptr<OptionSomeEscape::tree> t) {
  return std::make_optional<std::function<unsigned int(unsigned int)>>(
      [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      });
}

__attribute__((pure)) unsigned int OptionSomeEscape::apply_option(
    const std::optional<std::function<unsigned int(unsigned int)>> o,
    const unsigned int x) {
  if (o.has_value()) {
    const std::function<unsigned int(unsigned int)> &f = *o;
    return f(x);
  } else {
    return x;
  }
}
