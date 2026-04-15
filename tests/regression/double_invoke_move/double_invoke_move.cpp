#include <double_invoke_move.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// wrap_with takes TWO args. Partial application creates a closure.
/// Since t is stored in a constructor, wrap_with takes t as owned (by value).
std::shared_ptr<DoubleInvokeMove::tree>
DoubleInvokeMove::wrap_with(std::shared_ptr<DoubleInvokeMove::tree> t,
                            const unsigned int v) {
  return tree::node(t, v, tree::leaf());
}

__attribute__((pure)) unsigned int
DoubleInvokeMove::left_value(const std::shared_ptr<DoubleInvokeMove::tree> &t) {
  if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename DoubleInvokeMove::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename DoubleInvokeMove::tree::Leaf>(
            _sv0->v())) {
      return 0u;
    } else {
      const auto &_m0 =
          *std::get_if<typename DoubleInvokeMove::tree::Node>(&_sv0->v());
      return _m0.d_a1;
    }
  }
}
