#include "dropped_binder_in_instance_method.h"

std::optional<crane::obj>
Functorish_option(crane::fn<crane::obj(crane::obj)> f,
                  const std::optional<crane::obj> &o) {
  if (o.has_value()) {
    const auto &a = *o;
    return std::make_optional<crane::obj>(crane::obj(crane_call_erased(f, a)));
  } else {
    return std::optional<crane::obj>();
  }
}

std::optional<List<Nat>> plain(const std::optional<Nat> &o) {
  return fmapish<std::optional<crane::obj>, Nat, List<Nat>>(
      [](auto &&_ec0, std::optional<crane::obj> _ec1) {
        return Functorish_option(_ec0, _ec1);
      },
      [](const Nat &x) { return List<Nat>::cons(x, List<Nat>::nil()); }, o);
}

std::optional<List<Nat>> run(const std::optional<Nat> &o) {
  return Prov_nat::aid_to_prov(o);
}
