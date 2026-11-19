#include "record_field_carrier_alias.h"

template <typename CraneTcArg>
using crane_carrier_tc_968158098cbaa1b8 =
    Itree<RecordFieldCarrierAlias::noE, CraneTcArg>;

RecordFieldCarrierAlias::Holder RecordFieldCarrierAlias::mk(
    const std::type_identity_t<RecordFieldCarrierAlias::stateT<
        Nat, crane_carrier_tc_968158098cbaa1b8, bool>> &m) {
  return Holder{m, Nat::s(Nat::o())};
}
