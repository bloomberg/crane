#include "primed_identifier.h"

Nat twice_(const Nat &n) { return n.add(n); }

Nat PrimedIdentifier::use(const Nat &n) {
  return twice_(size<Nat>(Sized_nat_, n));
}
