#include "eta_partial_app_drops_targs.h"

std::optional<List<Nat>> run(const std::optional<Nat> &o) {
  return Fun_Mon<Mon_option>::template ffmap<Nat, List<Nat>>(
      [](const Nat &x) { return List<Nat>::cons(x, List<Nat>::nil()); }, o);
}
