#include "sibling_module_same_inductive.h"

/// Two sibling submodules each declare an inductive named t.  The second
/// declaration makes Crane emit a doubly-qualified, empty namespace component
/// for the first:
///
/// Nat SiblingModuleSameInductive::A::get(
/// const SiblingModuleSameInductive::A:: ::t &x)
///
/// error: expected unqualified-id
///
/// With only module A present the same file extracts correctly, so this is
/// a name-resolution collision between the siblings, not eponymy.
Nat SiblingModuleSameInductive::A::get(
    const SiblingModuleSameInductive::A:: ::t &x) {
  const auto &[a0] = x;
  return a0;
}

bool SiblingModuleSameInductive::B::get(
    const SiblingModuleSameInductive::B::t &x) {
  const auto &[a0] = x;
  return a0;
}

Nat SiblingModuleSameInductive::run(Nat n) {
  return A::get(A::t::mk(std::move(n)));
}

bool SiblingModuleSameInductive::run2(bool b) { return B::get(B::t::mk(b)); }
