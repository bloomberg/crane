#include "event_family_only_in_return_type.h"
#include <cassert>

// The oracle is the recovered event, not the build: nothing here fails to
// compile whichever way the family position is spelled, so what has to be
// checked is that the event survives the erasure and comes back at its own
// type.  See the .v for why [std::any] is that spelling.
int main() {
  auto t = EventFamilyOnlyInReturnType::run();
  const auto &vis = std::get<ITree<Nat>::Vis>(t->observe());
  UBE e = crane_event_as<UBE>(vis.effect);
  assert(std::holds_alternative<UBE::Throwub>(e.v()));

  // At a larger family the erased [subevent] still passes a bare [UBE], and
  // the event comes back at that type -- not at the sum.
  auto t2 = EventFamilyOnlyInReturnType::run_sum();
  const auto &vis2 = std::get<ITree<Nat>::Vis>(t2->observe());
  UBE e2 = crane_event_as<UBE>(vis2.effect);
  assert(std::holds_alternative<UBE::Throwub>(e2.v()));
  return 0;
}
