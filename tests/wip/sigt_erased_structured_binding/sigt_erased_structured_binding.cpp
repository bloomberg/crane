#include "sigt_erased_structured_binding.h"

Nat SigtErasedStructuredBinding::score(const SigT<std::any, std::any> &i) {
  auto [x, f] = i.projT2();
  return crane_call_erased(f, x);
}

Nat SigtErasedStructuredBinding::total(
    const List<SigT<std::any, std::any>> &l) {
  return l.template fold_left<Nat>(
      [](const Nat &a, const auto &i) { return a.add(score(i)); }, Nat::o());
}
