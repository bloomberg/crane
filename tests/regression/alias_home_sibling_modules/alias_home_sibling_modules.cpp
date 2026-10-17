#include "alias_home_sibling_modules.h"

template <typename CraneTcArg>
using crane_carrier_tc_3d272b5b88d953e4 =
    Itree<AliasHomeSiblingModules::A::e, CraneTcArg>;

AliasHomeSiblingModules::stateT<Nat, crane_carrier_tc_3d272b5b88d953e4, Nat>
AliasHomeSiblingModules::A::a_id(
    std::type_identity_t<AliasHomeSiblingModules::stateT<
        Nat, crane_carrier_tc_3d272b5b88d953e4, Nat>>
        m) {
  return m;
}

template <typename CraneTcArg>
using crane_carrier_tc_9540e08bcf9c9f2f =
    Itree<AliasHomeSiblingModules::B::e, CraneTcArg>;

AliasHomeSiblingModules::stateT<Nat, crane_carrier_tc_9540e08bcf9c9f2f, Nat>
AliasHomeSiblingModules::B::b_id(
    std::type_identity_t<AliasHomeSiblingModules::stateT<
        Nat, crane_carrier_tc_9540e08bcf9c9f2f, Nat>>
        m) {
  return m;
}
