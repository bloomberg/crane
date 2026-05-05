// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: Prop-erased module member `relation_on_X` must NOT appear
// in the generated header; compilation would fail otherwise.

#include "SepExtPropErasedUsing.h"

#include <cassert>

struct IntOT {
  using t = int;
};

int main() {
  // The non-Prop member eq_key must still be usable.
  using F = SepExtPropErasedUsing::FMapList<IntOT>;
  assert(F::eq_key(1, 2));
  return 0;
}
