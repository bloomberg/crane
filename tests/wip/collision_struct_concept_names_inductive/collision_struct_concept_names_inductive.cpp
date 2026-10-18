#include "collision_struct_concept_names_inductive.h"

bool PeanoNat::eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::eqb(*a0, *a00);
    }
  }
}

Nat CollisionStructConceptNamesInductive::first(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return a0;
  }
}
