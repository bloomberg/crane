#include "match_closure_escape.h"

/// BUG TRIGGER: match_arm_box
/// The partial application sum_values l inside a match arm creates a
/// & lambda capturing the match-bound variable _args (from std::visit).
/// This lambda is stored in a Box constructor argument.
/// return_captures_by_value does NOT handle lambdas inside constructor args.
/// When the visit lambda returns, _args goes out of scope, and the Box
/// holds a dangling reference to a destroyed shared_ptr.
MatchClosureEscape::fn_box
MatchClosureEscape::match_arm_box(const MatchClosureEscape::tree &t) {
  if (std::holds_alternative<typename MatchClosureEscape::tree::Leaf>(t.v())) {
    return fn_box::box([](uint64_t x) { return x; });
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MatchClosureEscape::tree::Node>(t.v());
    const MatchClosureEscape::tree &a0_value = *a0;
    return fn_box::box([=](uint64_t _x0) mutable -> uint64_t {
      return a0_value.sum_values(_x0);
    });
  }
}
