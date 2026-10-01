#include <hk_carrier_alias_applied_as_type.h>

#include <cassert>

int main() {
  two<Nat, List<Nat>> inner{Nat::o(), List<Nat>::nil()};
  modul<Nat, List<Nat>> m{
      List<two<Nat, List<Nat>>>::cons(inner, List<two<Nat, List<Nat>>>::nil())};
  auto r = HkCarrierAliasAppliedAsType::run(m);
  (void)r;
  return 0;
}
