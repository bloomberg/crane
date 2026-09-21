#include "erased_pair_pattern_probed_at_any.h"
#include <cassert>
#include <cstdio>

int main() {
  // [run] is only declared in the header; the defect is in its definition, so
  // the call is what makes the .cpp's template instantiate.
  pairs<Nat, box<Nat>> m{
      List<std::pair<ident, Nat>>::cons(
          std::make_pair(ident{Nat::o()}, Nat::s(Nat::s(Nat::s(Nat::s(
                                              Nat::o()))))),
          List<std::pair<ident, Nat>>::nil()),
      box<Nat>{Nat::s(Nat::o())}};
  auto r = run(m);
  assert(r.p_body.b_payload == false);

  printf("All erased_pair_pattern_probed_at_any tests passed!\n");
  return 0;
}
