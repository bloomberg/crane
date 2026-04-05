// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// Regression test: embed-based effect smart constructors extract validly.
// Verifies that smart constructors using embed with typeclass constraints
// generate valid C++ without explicit Crane Extract Inlined Constant mappings.

#include <embed_effect.h>

#include <cassert>

int main() {
  auto result = bug_main();
  // bug_main calls bug_create("hello") then bug_read()
  assert(get_create_count() == 1);
  assert(get_read_count() == 1);
  assert(result == 42);
  return 0;
}
