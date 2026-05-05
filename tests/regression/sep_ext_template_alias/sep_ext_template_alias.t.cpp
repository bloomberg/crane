// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: a module abbreviation (eta-reduced functor alias) must extract
// as a template using alias, not a bare using alias.  Previously,
// Module WFacts := WFacts_fun extracted as "using WFacts = WFacts_fun;" which
// is invalid C++ because WFacts_fun is a template struct.

#include "SepExtTemplateAlias.h"

#include <cassert>

struct IntOT {
  using t = int;
};

int main() {
  // Verify that WFacts_fun<IntOT> and WFacts<IntOT> both compile and have the
  // same foo type.
  using WF = SepExtTemplateAlias::WFacts_fun<IntOT>;
  using WFA = SepExtTemplateAlias::WFacts<IntOT>;
  static_assert(std::is_same_v<WF::foo, WFA::foo>);
  return 0;
}
