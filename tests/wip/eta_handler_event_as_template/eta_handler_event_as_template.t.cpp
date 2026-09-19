#include "eta_handler_event_as_template.h"

#include <cassert>

int main() {
  // [use n] threads the state through the eta-expanded handler unchanged.
  auto t = M::use(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
