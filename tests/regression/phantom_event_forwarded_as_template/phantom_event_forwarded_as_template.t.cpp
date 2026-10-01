#include "phantom_event_forwarded_as_template.h"

#include <cassert>

struct P {
  using ptr = uint64_t;
  static ptr zero_ptr() { return 0; }
  static Nat width() { return Nat::s(Nat::s(Nat::o())); }
};

int main() {
  auto defs = PhantomEventForwardedAsTemplate::use<P>();
  // A Crane list is a variant, not a container: non-emptiness is [Cons].
  using entries = decltype(defs);
  assert(std::holds_alternative<typename entries::Cons>(defs.v()));
  return 0;
}
