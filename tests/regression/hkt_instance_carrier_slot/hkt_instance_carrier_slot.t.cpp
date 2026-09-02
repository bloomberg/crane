#include <hkt_instance_carrier_slot.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(
      HktInstanceCarrierSlot::run(List<Nat>::cons(Nat::o(), List<Nat>::nil())).v()));
  return 0;
}
