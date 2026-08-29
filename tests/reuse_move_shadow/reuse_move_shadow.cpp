#include "reuse_move_shadow.h"

uint64_t ReuseMoveShadow::tree_sum(const ReuseMoveShadow::tree &t) {
  if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(t.v())) {
    const auto &[a0, a1, a2] =
        std::get<typename ReuseMoveShadow::tree::Node>(t.v());
    return ((a0 + tree_sum(*a1)) + tree_sum(*a2));
  } else {
    return UINT64_C(0);
  }
}

ReuseMoveShadow::tree ReuseMoveShadow::dup_left(ReuseMoveShadow::tree t,
                                                bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(
            t.v_mut())) {
      auto &[a0, a1, a2] =
          std::get<typename ReuseMoveShadow::tree::Node>(t.v_mut());
      return tree::node(std::move(a0), *a1, *a1);
    } else {
      return tree::leaf();
    }
  } else {
    return t;
  }
}
