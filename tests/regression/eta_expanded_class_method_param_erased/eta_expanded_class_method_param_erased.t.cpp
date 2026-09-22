#include "eta_expanded_class_method_param_erased.h"
#include <cassert>
#include <cstdio>

// The number of cells in a list, so the two builds can be compared without
// assuming anything about the pairs they hold.
static int len(const List<std::pair<Nat, Nat>> &l) {
  int n = 0;
  const List<std::pair<Nat, Nat>> *cur = &l;
  while (std::holds_alternative<List<std::pair<Nat, Nat>>::Cons>(cur->v())) {
    ++n;
    cur = std::get<List<std::pair<Nat, Nat>>::Cons>(cur->v()).l.get();
  }
  return n;
}

int main() {
  auto one = Nat::s(Nat::o());
  auto l = List<std::pair<Nat, Nat>>::cons({one, one},
                                           List<std::pair<Nat, Nat>>::nil());
  assert(len(build(l)) == len(build_saturated(l)));
  assert(len(partial(one, one, List<std::pair<Nat, Nat>>::nil())) == 1);
  printf("All eta_expanded_class_method_param_erased tests passed!\n");
  return 0;
}
