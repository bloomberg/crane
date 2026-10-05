// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <unit_namespace_a.h>
#include <unit_namespace_b.h>

#include <cassert>
#include <iostream>

// Both units define a [List]; each lives in its unit's namespace, so the two
// headers compose in one translation unit, and link in one program.
int main() {
  assert(unit_namespace_a::UnitNamespaceA::sum(unit_namespace_a::UnitNamespaceA::sample) == 6);
  assert(unit_namespace_b::UnitNamespaceB::length(unit_namespace_b::UnitNamespaceB::sample) == 2);
  std::cout << "unit_namespace: ok\n";
  return 0;
}
