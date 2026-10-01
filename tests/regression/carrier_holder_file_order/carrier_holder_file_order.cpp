#include "carrier_holder_file_order.h"

Itree<AllE<typename natParams::ptr, crane::obj>, std::pair<Nat, Nat>>
CarrierHolderFileOrder::first(std::monostate) {
  return HoStack::template get_st<natParams>(Nat::s(Nat::o()))(
      Nat::s(Nat::s(Nat::o())));
}
