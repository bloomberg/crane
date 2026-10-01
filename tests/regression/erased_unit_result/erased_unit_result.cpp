#include "erased_unit_result.h"

void ErasedUnitResult::touch(uint64_t) { return; }

bool ErasedUnitResult::is_tt(std::monostate) {
  {
    return true;
  }
}

bool ErasedUnitResult::through_sig(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p) {
  const auto &[x, a1] = p;
  const auto &[f, x0] = a1;
  return is_tt([&]() {
    crane::any_cast<std::monostate>(
        crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(x0));
    return std::monostate{};
  }());
}
