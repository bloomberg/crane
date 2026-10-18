#include "collision_child_function_before_constant.h"

Nat CollisionChildFunctionBeforeConstant::first(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return a0;
  }
}
