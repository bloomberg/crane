#include "option_closure_escape.h"

unsigned int OptionClosureEscape::sum_values(const OptionClosureEscape::tree &t,
                                             unsigned int x) {
  if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename OptionClosureEscape::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
            _sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename OptionClosureEscape::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename OptionClosureEscape::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// BUG: pair_escape stores a & lambda in a pair.
/// The lambda captures parameter t by reference.
/// When pair_escape returns, t is destroyed → dangling.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::pair_escape(OptionClosureEscape::tree t) {
  return std::make_pair(
      [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      },
      42u);
}

/// BUG: match_pair — & captures _args from visit scope.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
OptionClosureEscape::match_pair(const OptionClosureEscape::tree &t) {
  if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(t.v())) {
    return std::make_pair([](unsigned int x) { return x; }, 0u);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename OptionClosureEscape::tree::Node>(t.v());
    const OptionClosureEscape::tree &a0_value = *a0;
    return std::make_pair(
        [=](unsigned int _x0) mutable -> unsigned int {
          return sum_values(a0_value, _x0);
        },
        a1);
  }
}
