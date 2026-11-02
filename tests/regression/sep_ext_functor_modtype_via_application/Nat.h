#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <utility>
#include <variant>

#include "Datatypes.h"

namespace Nat {

Datatypes::Nat add(const Datatypes::Nat &n, Datatypes::Nat m);
bool eqb(const Datatypes::Nat &n, const Datatypes::Nat &m);

} // namespace Nat

#endif // INCLUDED_NAT
