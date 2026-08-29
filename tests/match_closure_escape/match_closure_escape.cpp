#include "match_closure_escape.h"

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
