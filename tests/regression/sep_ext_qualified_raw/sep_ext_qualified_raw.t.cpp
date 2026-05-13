// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: render_cpp_type_simple must handle Tqualified types so that
// raw string rendering (for clone/converting constructors) produces
// fully qualified names like "typename X::t" instead of bare "t".

#include "SepExtQualifiedRaw.h"

#include <cassert>

struct IntOrd {
  using t = int;
};

int main() {
  using M = SepExtQualifiedRaw::Make<IntOrd>;
  using FMap = M::Fmap<double>;

  auto empty = FMap::empty();
  assert(M::is_empty(empty) == true);

  auto n = FMap::node(1, 3.14, FMap::empty());
  assert(M::is_empty(n) == false);

  // Test converting copy constructor (Fmap<double> -> Fmap<float>)
  using FMapF = M::Fmap<float>;
  FMapF converted(n);
  assert(M::is_empty(converted) == false);

  return 0;
}
