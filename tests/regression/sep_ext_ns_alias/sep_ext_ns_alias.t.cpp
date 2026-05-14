// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: plain module alias must emit `using FooAlias = Foo;`
// (modules are C++ structs, so using-alias is correct).

#include "SepExtNsAlias.h"

#include <cassert>

int main() {
  // If the using alias compiled, we can access Foo::x through FooAlias.
  auto x = SepExtNsAlias::FooAlias::x;
  (void)x;
  return 0;
}
