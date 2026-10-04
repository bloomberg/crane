#include "polymorphic_helper.h"

Nat foo(Nat n, bool b) {
  return foo_crane_aux(std::move(n), n).add(foo_crane_aux(b, n));
}
