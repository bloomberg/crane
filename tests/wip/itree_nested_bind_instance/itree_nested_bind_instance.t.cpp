#include <itree_nested_bind_instance.h>

#include <cassert>

int main() {
  // g (Ret 2) binds twice and runs to 4.
  auto t = ItreeNestedBindInstance::use(Nat::s(Nat::s(Nat::o())));
  auto r = t->run();
  assert(std::holds_alternative<Nat::S>(r.v()));
  return 0;
}
