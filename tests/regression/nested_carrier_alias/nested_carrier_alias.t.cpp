#include <cassert>
#include <nested_carrier_alias.h>

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
  // The header compiles only if both carriers are declared where their
  // uses read them; stacked_id's signature is the use.
  auto id = &NestedCarrierAlias::stacked_id;
  assert(id != nullptr);
  assert(nat_to_int(NestedCarrierAlias::five) == 5);
  return 0;
}
