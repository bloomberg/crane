#include "collision_struct_concept_names_struct.h"

Nat CollisionStructConceptNamesStruct::head_or_zero(const List<Nat> &x0_) {
  return CollisionStructConceptNamesStruct::first(x0_);
}

Nat CollisionStructConceptNamesStruct::first(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return a0;
  }
}
