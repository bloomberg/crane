#include "eta_partial_app_drops_targs.h"
#include <cassert>
#include <cstdio>
#include <optional>

int main() {
  // [ffmap] is the eta-expanded partial application; [fconst] in the same
  // class is the control, fully applied over the same [liftM].
  auto r = run(std::optional<Nat>(Nat::s(Nat::o())));
  assert(r.has_value());

  auto e = run(std::optional<Nat>());
  assert(!e.has_value());

  printf("All eta_partial_app_drops_targs tests passed!\n");
  return 0;
}
