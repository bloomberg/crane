// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: sigT inside a functor must have consistent template
// parameters between the declaration type and the constructor call.

#include "SepExtSigtAny.h"

struct IntS {
  using t = int;
};

static_assert(SepExtSigtAny::S<IntS>);

int main() {
  const auto &v = SepExtSigtAny::MyMod<IntS>::ex();
  (void)v;
  return 0;
}
