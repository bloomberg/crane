#include <cassert>
#include <method_type_names_module_alias.h>

static int nat_to_int(const Nat &n) {
  int c = 0;
  Nat m = n;
  while (std::holds_alternative<typename Nat::S>(m.v())) {
    c++;
    m = *std::get<typename Nat::S>(m.v()).a0;
  }
  return c;
}

int main() {
  using M = MethodTypeNamesModuleAlias;
  assert(M::use);
  assert(nat_to_int(M::leaves) == 2);
  return 0;
}
