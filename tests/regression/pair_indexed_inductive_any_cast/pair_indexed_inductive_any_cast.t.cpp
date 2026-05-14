// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: accessing fst/snd of a pair field in a type-indexed inductive
// must emit std::any_cast<T> in generated C++ (not a bare std::any return).

#include "PairIndexedInductiveAnyCast.h"
#include "Datatypes.h"

#include <cassert>

using namespace PairIndexedInductiveAnyCast;

int main() {
  // Nat::s(Nat::s(Nat::s(Nat::o()))) = 3, Nat::s(Nat::o()) = 1
  Datatypes::Nat seven = Datatypes::Nat::s(Datatypes::Nat::s(
      Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
          Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o())))))));
  const auto p = Ops::make<int>(42, seven);
  const int  a = Ops::get_fst<int>(p);
  const Datatypes::Nat b = Ops::get_snd<int>(p);
  assert(a == 42);
  (void)b;
  return 0;
}
