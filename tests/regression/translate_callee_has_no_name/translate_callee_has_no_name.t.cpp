#include "translate_callee_has_no_name.h"
#include <cassert>

int main() {
  auto t = TranslateCalleeHasNoName::use(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
