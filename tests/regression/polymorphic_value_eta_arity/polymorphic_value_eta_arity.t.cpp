// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <polymorphic_value_eta_arity.h>
#include <cassert>

int main() {
  assert(PolymorphicValueEtaArity::through_idf == 5);
  assert(PolymorphicValueEtaArity::through_constf == 3);
  return 0;
}
