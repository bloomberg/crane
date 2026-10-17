#include "alias_home_enclosing_module.h"

template <typename CraneTcArg>
using crane_carrier_tc_837848e58ce0624f =
    Itree<AliasHomeEnclosingModule::outerE, CraneTcArg>;

AliasHomeEnclosingModule::stateT<Nat, crane_carrier_tc_837848e58ce0624f, Nat>
AliasHomeEnclosingModule::Inner::mixed(
    std::type_identity_t<AliasHomeEnclosingModule::stateT<
        Nat, crane_carrier_tc_837848e58ce0624f, Nat>>
        m) {
  return m;
}

template <typename CraneTcArg>
using crane_carrier_tc_a12b979d5713beee =
    Itree<AliasHomeEnclosingModule::Inner::noE, CraneTcArg>;

AliasHomeEnclosingModule::stateT<Nat, crane_carrier_tc_a12b979d5713beee, Nat>
AliasHomeEnclosingModule::Inner::Deeper::deep_outer(
    std::type_identity_t<AliasHomeEnclosingModule::stateT<
        Nat, crane_carrier_tc_a12b979d5713beee, Nat>>
        m) {
  return m;
}

AliasHomeEnclosingModule::stateT<bool, crane_carrier_tc_a12b979d5713beee, Nat>
AliasHomeEnclosingModule::after(
    std::type_identity_t<AliasHomeEnclosingModule::stateT<
        bool, crane_carrier_tc_a12b979d5713beee, Nat>>
        m) {
  return m;
}
