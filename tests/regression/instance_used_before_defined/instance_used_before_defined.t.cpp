#include <instance_used_before_defined.h>

#include <cassert>
#include <variant>

static Nat nat_of(unsigned n) {
  Nat r = Nat::o();
  for (unsigned i = 0; i < n; ++i) r = Nat::s(std::move(r));
  return r;
}

int main() {
  auto r = InstanceUsedBeforeDefined::use(nat_of(3));
  assert(std::holds_alternative<EOU<Nat>::Raise_ret>(r.v()));
  return 0;
}
