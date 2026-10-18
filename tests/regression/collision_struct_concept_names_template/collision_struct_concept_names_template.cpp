#include "collision_struct_concept_names_template.h"

Nat CollisionStructConceptNamesTemplate::helper(const Nat &n) {
  return n.add(Nat::s(Nat::o()));
}

Nat CollisionStructConceptNamesTemplate::size(const Shape &x) {
  if (std::holds_alternative<typename Shape::Circle>(x.v())) {
    const auto &[r0, c] = std::get<typename Shape::Circle>(x.v());
    return CollisionStructConceptNamesTemplate::helper(r0);
  } else {
    const auto &[s0, t0] = std::get<typename Shape::Square>(x.v());
    return s0.add(CollisionStructConceptNamesTemplate::size(*t0));
  }
}

Nat CollisionStructConceptNamesTemplate::first(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return a0;
  }
}

Nat CollisionStructConceptNamesTemplate::head_or_zero(const List<Nat> &x0_) {
  return CollisionStructConceptNamesTemplate::first(x0_);
}
