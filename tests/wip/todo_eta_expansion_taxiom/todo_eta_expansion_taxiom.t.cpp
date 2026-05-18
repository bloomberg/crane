// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: TODO from src/mlutil.ml:964/976/1585 — Taxiom as lambda parameter type.
// If eta-expansion triggers the Taxiom path, match branch parameters would have
// the "axiom" type in C++, causing compilation errors.
// Bug status: UNDER INVESTIGATION (simple patterns may not trigger this path).

#include "todo_eta_expansion_taxiom.h"

#include <cassert>

int main() {
  auto s = TodoEtaExpansionTaxiom::test_swap;
  assert(TodoEtaExpansionTaxiom::test_fst == 42u);
  (void)s;
  return 0;
}
