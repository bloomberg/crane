#include <itree_poly_event_arg.h>

#include <cassert>

int main() {
  // f (Ret 2) runs to 3.
  auto t = ItreePolyEventArg::use(Nat::s(Nat::s(Nat::o())));
  auto r = t->run();
  assert(std::holds_alternative<Nat::S>(r.v()));
  return 0;
}
