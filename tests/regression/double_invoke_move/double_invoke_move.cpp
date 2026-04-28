#include <double_invoke_move.h>

/// wrap_with takes TWO args. Partial application creates a closure.
/// Since t is stored in a constructor, wrap_with takes t as owned (by value).
__attribute__((pure)) DoubleInvokeMove::tree
DoubleInvokeMove::wrap_with(DoubleInvokeMove::tree t, unsigned int v) {
  return tree::node(std::move(t), v, tree::leaf());
}

__attribute__((pure)) unsigned int
DoubleInvokeMove::left_value(const DoubleInvokeMove::tree &t) {
  if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename DoubleInvokeMove::tree::Node>(t.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(
            _sv0.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename DoubleInvokeMove::tree::Node>(_sv0.v());
      return d_a10;
    }
  }
}
