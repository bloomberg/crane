#include "hk_constraint_carrier_two_params.h"

outer1<Nat, two<Nat, List<Nat>>>
HkConstraintCarrierTwoParams::run(const outer1<Nat, two<Nat, List<Nat>>> &m) {
  return TFunctor_outer1<TFunctor_list, TFunctor_two<TFunctor_list>>::
      template tfmap<Nat, Nat>([](const Nat &x) { return Nat::s(x); }, m);
}
