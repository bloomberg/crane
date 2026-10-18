#include "moved_struct_method_after_collision.h"

Nat MovedStructMethodAfterCollision::Helpers::inc(const Nat &n) {
  return Nat::s(n);
}

Nat MovedStructMethodAfterCollision::first(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return a0;
  }
}

Nat MovedStructMethodAfterCollision::head_or_zero(const List<Nat> &x0_) {
  return MovedStructMethodAfterCollision::first(x0_);
}
