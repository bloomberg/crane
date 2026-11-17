#include <cassert>
#include <alias_home_constructor_field.h>

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
  // The header compiles only if each carrier is declared where the
  // constructor fields that use it are read.
  auto tag = &AliasHomeConstructorField::Inner::tag;
  assert(tag != nullptr);
  assert(nat_to_int(AliasHomeConstructorField::five) == 5);
  return 0;
}
