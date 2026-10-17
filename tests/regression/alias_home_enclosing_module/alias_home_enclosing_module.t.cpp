#include <cassert>
#include <alias_home_enclosing_module.h>

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
  // The header compiles only if each carrier is declared where its use
  // reads it; the three signatures are the uses.
  auto mixed = &AliasHomeEnclosingModule::Inner::mixed;
  auto deep = &AliasHomeEnclosingModule::Inner::Deeper::deep_outer;
  auto after = &AliasHomeEnclosingModule::after;
  assert(mixed != nullptr && deep != nullptr && after != nullptr);
  assert(nat_to_int(AliasHomeEnclosingModule::five) == 5);
  return 0;
}
