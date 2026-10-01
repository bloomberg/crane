#include <itree_ret_go.h>

#include <cassert>

int main() {
  // bind (Ret 2) (fun a => Ret (S a)) runs to 3.
  auto t = ItreeRetGo::use(Nat::s(Nat::s(Nat::o())));
  auto r = t->run();
  assert(std::holds_alternative<Nat::S>(r.v()));
  return 0;
}
