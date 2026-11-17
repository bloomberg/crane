#include "carrier_holder_file_order.h"

Itree<AllE<typename natParams::ptr, crane::obj>, std::pair<Nat, Nat>>
CarrierHolderFileOrder::first() {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto get_st_1 =
      crane::immortal(HoStack::template get_st<natParams>(Nat::s(Nat::o())));
  return get_st_1(Nat::s(Nat::s(Nat::o())));
}
