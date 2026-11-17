#include <cassert>
#include <record_field_carrier_alias.h>

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
  // The header compiles only if the carrier is declared ahead of the
  // record's field that names it.
  auto mk = &RecordFieldCarrierAlias::mk;
  assert(mk != nullptr);
  assert(nat_to_int(RecordFieldCarrierAlias::five) == 5);
  return 0;
}
