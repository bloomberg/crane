#include "applied_typename_not_hk.h"
#include <cassert>

int main() {
  auto t = AppliedTypenameNotHk::use(Nat::s(Nat::o()));
  assert(t);
  return 0;
}
