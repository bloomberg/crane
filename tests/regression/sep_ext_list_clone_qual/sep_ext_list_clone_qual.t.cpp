// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: the iterative clone() loop body for an inductive with a
// `list<Self>` field must use `Datatypes::List<T>`, not bare `List<T>`.
// (clone() was removed; this now tests that Forest constructors and
// qualified list names are emitted correctly.)

#include "SepExtListCloneQual.h"

#include <cassert>

int main() {
  // Build a small forest and verify constructors work correctly.
  auto leaf = SepExtListCloneQual::Forest<int>::leaf();
  auto node = SepExtListCloneQual::Forest<int>::node(
      42,
      Datatypes::List<SepExtListCloneQual::Forest<int>>::cons(leaf, {}));

  assert(std::holds_alternative<SepExtListCloneQual::Forest<int>::Node>(
      node.v()));
  return 0;
}
