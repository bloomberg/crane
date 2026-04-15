#include <partial_app_move.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// A function taking two args: tree -> nat -> nat.
/// Partial application of this to a tree creates a
/// closure nat -> nat in C++ via & lambda.
__attribute__((pure)) unsigned int
PartialAppMove::sum_values(const std::shared_ptr<PartialAppMove::tree> &t,
                           const unsigned int x) {
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(t->v())) {
    return x;
  } else {
    const auto &_m = *std::get_if<typename PartialAppMove::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(
            _sv0->v())) {
      return (_m.d_a1 + x);
    } else {
      const auto &_m0 =
          *std::get_if<typename PartialAppMove::tree::Node>(&_sv0->v());
      auto &&_sv1 = _m.d_a2;
      if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(
              _sv1->v())) {
        return (_m0.d_a1 + x);
      } else {
        const auto &_m1 =
            *std::get_if<typename PartialAppMove::tree::Node>(&_sv1->v());
        return (((_m0.d_a1 + _m1.d_a1) + _m.d_a1) + x);
      }
    }
  }
}

/// Wrap a tree inside another Node.
/// In C++, this calls tree::node() which has rvalue ref overloads.
/// If escape analysis adds std::move(t) here, the move is REAL.
std::shared_ptr<PartialAppMove::tree>
PartialAppMove::wrap(std::shared_ptr<PartialAppMove::tree> t) {
  return tree::node(t, 0u, tree::leaf());
}

/// BUG TRIGGER: partial application creates a & lambda capturing t,
/// then t is passed to a constructor (actually moved via rvalue ref),
/// then the lambda accesses the moved-from t.
__attribute__((pure)) unsigned int
PartialAppMove::trigger_bug(std::shared_ptr<PartialAppMove::tree> t) {
  std::function<unsigned int(unsigned int)> f =
      [=](unsigned int _x0) mutable -> unsigned int {
    return sum_values(t, _x0);
  };
  std::shared_ptr<PartialAppMove::tree> w = wrap(std::move(t));
  if (std::holds_alternative<typename PartialAppMove::tree::Leaf>(w->v())) {
    return f(0u);
  } else {
    return f(99u);
  }
}
