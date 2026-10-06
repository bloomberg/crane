#include "hk_carrier_alias_applied_as_type.h"

modul<Nat, List<Nat>>
HkCarrierAliasAppliedAsType::run(const modul<Nat, List<Nat>> &m) {
  return TFunctor_modul<TFunctor_list, TFunctor_two<TFunctor_list>>::
      template tfmap<Nat, Nat>([](const Nat &x) { return Nat::s(x); }, m);
}
