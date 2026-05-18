#include "double_invoke_move.h"

/// wrap_with takes TWO args. Partial application creates a closure.
/// Since t is stored in a constructor, wrap_with takes t as owned (by value).
DoubleInvokeMove::tree DoubleInvokeMove::wrap_with(DoubleInvokeMove::tree t,
                                                   uint64_t v) {
  return tree::node(std::move(t), v, tree::leaf());
}

uint64_t DoubleInvokeMove::left_value(const DoubleInvokeMove::tree &t) {
  if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename DoubleInvokeMove::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(
            _sv0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename DoubleInvokeMove::tree::Node>(_sv0.v());
      return a10;
    }
  }
}
