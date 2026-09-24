#include <cassert>
#include <pair_component_erased_in_destructuring_binder.h>

int main() {
  using Elt = std::pair<List<std::pair<Nat, Nat>>, List<Nat>>;
  using NS = PairComponentErasedInDestructuringBinder;
  assert(std::holds_alternative<EOU<Elt>::Ok>(NS::run.v()));
  return 0;
}
