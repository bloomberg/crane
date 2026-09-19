#include "phantom_alias_targ_unbound.h"

#include <cassert>

struct P {
  static Nat width() { return Nat::s(Nat::s(Nat::o())); }
};

int main() {
  // A one-element association list whose payload is the phantom-aliased
  // semantic function.
  auto defs = Qs::use<P>();
  assert(!defs.empty());
  return 0;
}
