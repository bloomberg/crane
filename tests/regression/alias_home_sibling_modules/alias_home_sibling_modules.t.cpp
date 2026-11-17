#include <cassert>
#include <alias_home_sibling_modules.h>

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
  // The header compiles only if each module declares the carrier its own
  // signature reads.
  auto a = &AliasHomeSiblingModules::A::a_id;
  auto b = &AliasHomeSiblingModules::B::b_id;
  assert(a != nullptr && b != nullptr);
  assert(nat_to_int(AliasHomeSiblingModules::five) == 5);
  return 0;
}
