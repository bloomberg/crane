#include "arena_non_atomic_rc.h"

/// A recursive type of a unit with both the scoped arena and non-atomic
/// reference counts: its constructors allocate a child through the
/// non-atomic pointer's own arena-aware factory, crane::rc<T>::make.
Nat ArenaNonAtomicRc::size(const ArenaNonAtomicRc::tree &t) {
  if (std::holds_alternative<typename ArenaNonAtomicRc::tree::Leaf>(t.v())) {
    return Nat::s(Nat::o());
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ArenaNonAtomicRc::tree::Node>(t.v());
    return Nat::s(Nat::o()).add(size(*a0)).add(size(*a2));
  }
}

ArenaNonAtomicRc::tree
ArenaNonAtomicRc::mirror(const ArenaNonAtomicRc::tree &t) {
  if (std::holds_alternative<typename ArenaNonAtomicRc::tree::Leaf>(t.v())) {
    return tree::leaf();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ArenaNonAtomicRc::tree::Node>(t.v());
    return tree::node(mirror(*a2), a1, mirror(*a0));
  }
}
