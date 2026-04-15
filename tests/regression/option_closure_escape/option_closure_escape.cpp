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
    const auto &_m =
        *std::get_if<typename OptionClosureEscape::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
            _sv0->v())) {
      return (_m.d_a1 + x);
    } else {
      const auto &_m0 =
          *std::get_if<typename OptionClosureEscape::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m.d_a2;
      if (std::holds_alternative<typename OptionClosureEscape::tree::Leaf>(
              _sv1->v())) {
        return (_m0.d_a1 + x);
      } else {
        const auto &_m1 =
            *std::get_if<typename OptionClosureEscape::tree::Node>(&_sv1->v());
        return (((_m0.d_a1 + _m1.d_a1) + _m.d_a1) + x);
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
    const auto &_m =
        *std::get_if<typename OptionClosureEscape::tree::Node>(&t->v());
    return std::make_pair(
        [=](unsigned int _x0) mutable -> unsigned int {
          return sum_values(_m.d_a0, _x0);
        },
        _m.d_a1);
  }
}
