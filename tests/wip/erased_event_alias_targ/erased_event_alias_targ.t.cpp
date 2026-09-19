#include "erased_event_alias_targ.h"
#include <cassert>

int main() {
  auto l = List<Nat>::cons(Nat::o(), List<Nat>::nil());
  auto t = ErasedEventAliasTarg::use(l);
  assert(t != nullptr);
  return 0;
}
