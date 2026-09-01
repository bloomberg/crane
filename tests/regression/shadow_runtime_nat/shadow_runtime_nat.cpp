#include "shadow_runtime_nat.h"

::Nat ShadowRuntimeNat::toNat(const ShadowRuntimeNat::Nat &n) {
  if (std::holds_alternative<typename ShadowRuntimeNat::Nat::O2>(n.v())) {
    return ::Nat::o();
  } else {
    const auto &[a0] = std::get<typename ShadowRuntimeNat::Nat::S2>(n.v());
    return ::Nat::s(toNat(*a0));
  }
}
