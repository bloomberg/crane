#include <cassert>
#include <record_module_function_qualifier.h>

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
  using M = RecordModuleFunctionQualifier;
  assert(nat_to_int(M::empty.size) == 0);
  assert(!M::empty.full);
  assert(nat_to_int(M::picked) == 4);
  assert(nat_to_int(M::large) == 2);
  return 0;
}
