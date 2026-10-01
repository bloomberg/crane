#include <hk_constraint_carrier_two_params.h>

#include <cassert>

int main() {
  two<Nat, List<Nat>> inner{Nat::o(), List<Nat>::nil()};
  outer1<Nat, two<Nat, List<Nat>>> m{inner};
  auto r = HkConstraintCarrierTwoParams::run(m);
  (void)r;
  return 0;
}
