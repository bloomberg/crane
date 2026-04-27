#include <match_ctor_closure.h>

/// BUG HYPOTHESIS: Match arm stores a partial application (closure)
/// in a constructor. The lambda captures a PATTERN VARIABLE (_args.d_a0)
/// by & reference. When the visit lambda returns, _args is destroyed
/// but the fn_box retains the closure with a dangling reference.
__attribute__((pure)) MatchCtorClosure::fn_box
MatchCtorClosure::match_and_box(const MatchCtorClosure::tree &t) {
  if (std::holds_alternative<typename MatchCtorClosure::tree::Leaf>(t.v())) {
    return fn_box::box([](unsigned int x) { return x; });
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MatchCtorClosure::tree::Node>(t.v());
    MatchCtorClosure::tree d_a0_value = *(d_a0);
    return fn_box::box([=](unsigned int _x0) mutable -> unsigned int {
      return d_a0_value.sum_values(_x0);
    });
  }
}
