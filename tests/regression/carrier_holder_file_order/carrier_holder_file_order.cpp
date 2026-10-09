#include "carrier_holder_file_order.h"

Itree<AllE<typename natParams::ptr, crane::obj>, std::pair<Nat, Nat>>
CarrierHolderFileOrder::first(std::monostate) {
  static const auto get_st_1 =
      crane::immortal(HoStack::template get_st<natParams>(Nat::s(Nat::o())));
  return get_st_1(Nat::s(Nat::s(Nat::o())));
}
