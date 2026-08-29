#include "match_ctor_closure.h"

MatchCtorClosure::fn_box
MatchCtorClosure::match_and_box(const MatchCtorClosure::tree &t) {
  if (std::holds_alternative<typename MatchCtorClosure::tree::Leaf>(t.v())) {
    return fn_box::box([](uint64_t x) { return x; });
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MatchCtorClosure::tree::Node>(t.v());
    const MatchCtorClosure::tree &a0_value = *a0;
    return fn_box::box([=](uint64_t _x0) mutable -> uint64_t {
      return a0_value.sum_values(_x0);
    });
  }
}
