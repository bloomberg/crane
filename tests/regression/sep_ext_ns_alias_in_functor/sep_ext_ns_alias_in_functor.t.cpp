// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: Module R := Inner inside a functor body must not generate
// "using R = Inner;" (invalid when Inner is a C++ namespace/non-type).

#include "SepExtNsAliasInFunctor.h"

struct IntS {
  using t = int;
};

int main() {
  const auto v = SepExtNsAliasInFunctor::MyFunctor<IntS>::use_r;
  (void)v;
  return 0;
}
