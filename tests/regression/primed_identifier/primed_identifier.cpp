#include "primed_identifier.h"

Nat twice_(Nat n) { return n.add(n); }

Nat PrimedIdentifier::use(const Nat &n) { return twice_(Sized_nat_::size(n)); }
