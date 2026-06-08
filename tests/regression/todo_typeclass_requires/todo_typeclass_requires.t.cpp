// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: TODO from src/translation.ml:11066 — typeclass requires clause not generated.
// When a template takes a typeclass parameter (_tcI0), it should have a
// `requires Numeric<_tcI0, T1>` constraint but currently doesn't.
// This test passes today (code works without the constraint) but serves as a
// regression test for when the requires clause is implemented.
// Bug status: DOCUMENTED (missing constraint, code compiles and runs correctly).

#include "todo_typeclass_requires.h"

#include <cassert>

int main() {
  assert(TodoTypeclassRequires::test_result == 14u);
  return 0;
}
