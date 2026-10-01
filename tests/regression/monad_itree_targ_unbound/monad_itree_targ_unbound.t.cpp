#include "monad_itree_targ_unbound.h"

#include <cassert>

struct P {
  static Nat width() { return Nat::s(Nat::s(Nat::o())); }
};

int main() {
  // [use n] runs the handler at state [n]; for [n <> 0] it returns the pair
  // [(n + 2, n)] after the [step 1] update, with no failure event.
  auto t = Qf::use<P>(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
