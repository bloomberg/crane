#include "dropped_binder_in_instance_method.h"

std::optional<List<Nat>> plain(const std::optional<Nat> &o) {
  return Functorish_option::template fmapish<Nat, List<Nat>>(
      [](const Nat &x) { return List<Nat>::cons(x, List<Nat>::nil()); }, o);
}

std::optional<List<Nat>> run(const std::optional<Nat> &o) {
  return Prov_nat::aid_to_prov(o);
}
