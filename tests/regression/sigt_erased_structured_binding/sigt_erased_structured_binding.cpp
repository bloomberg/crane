#include "sigt_erased_structured_binding.h"

Nat SigtErasedStructuredBinding::score(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &i) {
  const auto &[x, f] =
      crane::any_cast<std::pair<crane::obj, crane::obj>>(i.projT2());
  return crane::any_cast<Nat>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(x));
}

Nat SigtErasedStructuredBinding::total(
    const List<SigT<crane::obj, std::pair<crane::obj, crane::obj>>> &l) {
  return l.template fold_left<Nat>(
      [](const Nat &a, SigtErasedStructuredBinding::item i) {
        return a.add(score(i));
      },
      Nat::o());
}
