#include <match_closure_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// BUG TRIGGER: match_arm_box
/// The partial application sum_values l inside a match arm creates a
/// & lambda capturing the match-bound variable _args (from std::visit).
/// This lambda is stored in a Box constructor argument.
/// return_captures_by_value does NOT handle lambdas inside constructor args.
/// When the visit lambda returns, _args goes out of scope, and the Box
/// holds a dangling reference to a destroyed shared_ptr.
__attribute__((pure)) MatchClosureEscape::fn_box
MatchClosureEscape::match_arm_box(const MatchClosureEscape::tree &t) {
  if (std::holds_alternative<typename MatchClosureEscape::tree::Leaf>(t.v())) {
    return fn_box::box([](unsigned int x) { return x; });
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MatchClosureEscape::tree::Node>(t.v());
    MatchClosureEscape::tree d_a0_value =
        clone_as_value<MatchClosureEscape::tree>(d_a0);
    return fn_box::box([=](unsigned int _x0) mutable -> unsigned int {
      return d_a0_value.sum_values(_x0);
    });
  }
}
