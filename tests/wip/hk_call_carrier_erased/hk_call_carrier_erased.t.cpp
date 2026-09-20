#include <hk_call_carrier_erased.h>

#include <cassert>
#include <variant>

int main() {
  // Bumping through the list instance leaves the boxes in place.
  auto l = List<box<Nat>>::cons(box<Nat>{Nat::o()}, List<box<Nat>>::nil());
  auto r = HkCallCarrierErased::on_boxes(l);
  assert(std::holds_alternative<List<box<Nat>>::Cons>(r.v()));
  return 0;
}
