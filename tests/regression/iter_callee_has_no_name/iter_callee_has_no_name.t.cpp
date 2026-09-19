#include "iter_callee_has_no_name.h"
#include <cassert>

int main() {
  auto t = IterCalleeHasNoName::countdown(Nat::s(Nat::s(Nat::o())));
  assert(t != nullptr);
  return 0;
}
