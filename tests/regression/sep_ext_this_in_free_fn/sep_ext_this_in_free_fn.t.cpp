// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: List.length used as HOF arg in a free function template
// must generate a lambda wrapper, not `this->length()`.

#include "SepExtThisInFreeFn.h"

#include <cassert>
#include <vector>

struct UnitS {
  using t = int;
};

int main() {
  using F = SepExtThisInFreeFn::FreeFn<UnitS>;

  Datatypes::List<Datatypes::List<uint64_t>> xss{};
  auto result = F::map_lengths<uint64_t>(xss);
  (void)result;
  return 0;
}
