#include "dropped_binder_in_instance_method.h"

std::optional<std::any> Functorish_option(std::function<std::any(std::any)> f,
                                          const std::optional<std::any> &o) {
  if (o.has_value()) {
    const auto &a = *o;
    return std::make_optional<std::any>(std::any(crane_call_erased(f, a)));
  } else {
    return std::optional<std::any>();
  }
}

std::optional<List<Nat>> plain(const std::optional<Nat> &o) {
  return fmapish<std::optional>(
      [](auto &&_ec0, std::optional<std::any> _ec1) {
        return Functorish_option(_ec0, _ec1);
      },
      [](Nat x) { return List<Nat>::cons(x, List<Nat>::nil()); }, o);
}

std::optional<List<Nat>> run(const std::optional<Nat> &o) {
  return Prov_nat::aid_to_prov(o);
}
