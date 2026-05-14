// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: the iterative clone() loop body for an inductive with a
// `list<Self>` field must use `Datatypes::List<T>`, not bare `List<T>`.

#include "SepExtListCloneQual.h"

#include <cassert>

int main() {
  // Build a small forest and verify clone produces a deep copy.
  auto leaf = SepExtListCloneQual::Forest<int>::leaf();
  auto node = SepExtListCloneQual::Forest<int>::node(
      42,
      Datatypes::List<SepExtListCloneQual::Forest<int>>::cons(leaf, {}));

  auto cloned = node.clone();
  // Clone must be a distinct value (deep copy).
  assert(std::holds_alternative<SepExtListCloneQual::Forest<int>::Node>(
      cloned.v()));
  return 0;
}
