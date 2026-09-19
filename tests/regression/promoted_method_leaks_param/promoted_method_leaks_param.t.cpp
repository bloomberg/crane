#include "promoted_method_leaks_param.h"
#include <cassert>

int main() {
  auto l = List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil());
  auto t = PromotedMethodLeaksParam::use(l);
  assert(t != nullptr);
  return 0;
}
