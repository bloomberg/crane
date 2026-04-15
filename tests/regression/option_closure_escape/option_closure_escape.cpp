#include <option_closure_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int OptionClosureEscape::sum_values(
    const std::shared_ptr<OptionClosureEscape::tree> &t, const unsigned int x) {
  if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
          t->v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename OptionClosureEscape::tree::Node>(t->v());
    if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
            d_a0->v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename OptionClosureEscape::tree::Node>(d_a0->v());
      if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
              d_a2->v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename OptionClosureEscape::tree::Node>(d_a2->v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// BUG: pair_escape stores a & lambda in a pair.
/// The lambda captures parameter t by reference.
/// When pair_escape returns, t is destroyed → dangling.
__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::pair_escape(std::shared_ptr<OptionClosureEscape::tree> t) {
  return std::make_pair(
      [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      },
      42u);
}

/// BUG: match_pair — & captures _args from visit scope.
__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::match_pair(
    const std::shared_ptr<OptionClosureEscape::tree> &t) {
  if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
          t->v())) {
    return std::make_pair([](const unsigned int x) { return x; }, 0u);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename OptionClosureEscape::tree::Node>(t->v());
    return std::make_pair(
        [=](unsigned int _x0) mutable -> unsigned int {
          return sum_values(d_a0, _x0);
        },
        d_a1);
  }
}
