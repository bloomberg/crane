#include "hkt_instance_carrier_slot.h"

Nat HktInstanceCarrierSlot::run(const List<Nat> &l) {
  return HktInstanceCarrierSlot::SL::template sz<Nat>(l);
}
