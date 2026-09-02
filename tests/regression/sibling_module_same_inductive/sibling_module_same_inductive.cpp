#include "sibling_module_same_inductive.h"

/// Two sibling submodules each declare an inductive named t.  Both are
/// nested structs, so neither shadows a global-scope t; the out-of-line
/// definitions must stay plainly qualified:
///
/// Nat SiblingModuleSameInductive::A::get(
/// const SiblingModuleSameInductive::A::t &x)
Nat SiblingModuleSameInductive::A::get(
    const SiblingModuleSameInductive::A:: ::t &x) {
  const auto &[a0] = x;
  return a0;
}

bool SiblingModuleSameInductive::B::get(
    const SiblingModuleSameInductive::B:: ::t &x) {
  const auto &[a0] = x;
  return a0;
}

Nat SiblingModuleSameInductive::run(Nat n) {
  return A::get(A::t::mk(std::move(n)));
}

bool SiblingModuleSameInductive::run2(bool b) { return B::get(B::t::mk(b)); }
