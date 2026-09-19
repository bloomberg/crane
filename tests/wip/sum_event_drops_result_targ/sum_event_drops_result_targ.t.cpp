#include "sum_event_drops_result_targ.h"
#include <cassert>

int main() {
  auto l = List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil());
  auto t = SumEventDropsResultTarg::use(l);
  assert(t != nullptr);
  return 0;
}
