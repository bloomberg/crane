#include "handler_case_has_no_name.h"
#include <cassert>

int main() {
  auto t = HandlerCaseHasNoName::use(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
