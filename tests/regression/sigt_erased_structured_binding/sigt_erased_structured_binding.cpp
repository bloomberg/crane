#include "sigt_erased_structured_binding.h"

Nat SigtErasedStructuredBinding::score(
    const SigT<std::any, std::pair<std::any, std::any>> &i) {
  const auto &[x, f] = std::any_cast<std::pair<std::any, std::any>>(i.projT2());
  return std::any_cast<Nat>(
      std::any_cast<std::function<std::any(std::any)>>(f)(x));
}

Nat SigtErasedStructuredBinding::total(
    const List<SigT<std::any, std::pair<std::any, std::any>>> &l) {
  return l.template fold_left<Nat>(
      [](const Nat &a, const auto &i) { return a.add(score(i)); }, Nat::o());
}
