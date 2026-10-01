#include "phantom_alias_targ_unbound.h"

#include <cassert>

struct P {
  static Nat width() { return Nat::s(Nat::s(Nat::o())); }
};

int main() {
  // A one-element association list whose payload is the phantom-aliased
  // semantic function.
  auto defs = Qs::use<P>();
  // A Crane list is a variant, not a container: non-emptiness is [Cons].
  using entries = decltype(defs);
  assert(std::holds_alternative<typename entries::Cons>(defs.v()));
  return 0;
}
