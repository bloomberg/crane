#include <partial_app_move.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// A function taking two args: tree -> nat -> nat.
/// Partial application of this to a tree creates a
/// closure nat -> nat in C++ via & lambda.
__attribute__((pure)) unsigned int
PartialAppMove::sum_values(const PartialAppMove::tree &t, unsigned int x) {
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename PartialAppMove::tree::Node>(t.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(_sv0.v())) {
      return (d_a1 + x);
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename PartialAppMove::tree::Node>(_sv0.v());
      auto &&_sv1 = *(d_a2);
      if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(
              _sv1.v())) {
        return (d_a10 + x);
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename PartialAppMove::tree::Node>(_sv1.v());
        return (((d_a10 + d_a11) + d_a1) + x);
      }
    }
  }
}

/// Wrap a tree inside another Node.
/// In C++, this calls tree::node() which has rvalue ref overloads.
/// If escape analysis adds std::move(t) here, the move is REAL.
__attribute__((pure)) PartialAppMove::tree
PartialAppMove::wrap(PartialAppMove::tree t) {
  return tree::node(t, 0u, tree::leaf());
}

/// BUG TRIGGER: partial application creates a & lambda capturing t,
/// then t is passed to a constructor (actually moved via rvalue ref),
/// then the lambda accesses the moved-from t.
__attribute__((pure)) unsigned int
PartialAppMove::trigger_bug(PartialAppMove::tree t) {
  std::function<unsigned int(unsigned int)> f =
      [=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  };
  PartialAppMove::tree w = wrap(t);
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(w.v())) {
    return f(0u);
  } else {
    return f(99u);
  }
}
