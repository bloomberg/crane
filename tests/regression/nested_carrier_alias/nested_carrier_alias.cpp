#include "nested_carrier_alias.h"

template <typename CraneTcArg>
using crane_carrier_tc_f4f690a9ece556dd =
    Itree<NestedCarrierAlias::noE, CraneTcArg>;
template <typename CraneTcArg>
using crane_carrier_tc_4785a9b373278e5f =
    NestedCarrierAlias::stateT<bool, crane_carrier_tc_f4f690a9ece556dd,
                               CraneTcArg>;

NestedCarrierAlias::stateT<Nat, crane_carrier_tc_4785a9b373278e5f, Nat>
NestedCarrierAlias::stacked_id(
    std::type_identity_t<
        NestedCarrierAlias::stateT<Nat, crane_carrier_tc_4785a9b373278e5f, Nat>>
        m) {
  return m;
}
