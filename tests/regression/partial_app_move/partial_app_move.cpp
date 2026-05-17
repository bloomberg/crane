#include "partial_app_move.h"

/// A function taking two args: tree -> nat -> nat.
/// Partial application of this to a tree creates a
/// closure nat -> nat in C++ via & lambda.
uint64_t PartialAppMove::sum_values(const PartialAppMove::tree &t, uint64_t x) {
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(t.v())) {
    return x;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename PartialAppMove::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(_sv0.v())) {
      return (a1 + x);
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename PartialAppMove::tree::Node>(_sv0.v());
      auto &&_sv1 = *a2;
      if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(
              _sv1.v())) {
        return (a10 + x);
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename PartialAppMove::tree::Node>(_sv1.v());
        return (((a10 + a11) + a1) + x);
      }
    }
  }
}

/// Wrap a tree inside another Node.
/// In C++, this calls tree::node() which has rvalue ref overloads.
/// If escape analysis adds std::move(t) here, the move is REAL.
PartialAppMove::tree PartialAppMove::wrap(PartialAppMove::tree t) {
  return tree::node(std::move(t), UINT64_C(0), tree::leaf());
}

/// BUG TRIGGER: partial application creates a & lambda capturing t,
/// then t is passed to a constructor (actually moved via rvalue ref),
/// then the lambda accesses the moved-from t.
uint64_t PartialAppMove::trigger_bug(PartialAppMove::tree t) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t _x0) mutable -> uint64_t {
    return sum_values(t, _x0);
  };
  PartialAppMove::tree w = wrap(std::move(t));
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(w.v_mut())) {
    return f(UINT64_C(0));
  } else {
    return f(UINT64_C(99));
  }
}
