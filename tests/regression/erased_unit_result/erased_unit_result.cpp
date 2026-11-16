#include "erased_unit_result.h"

void ErasedUnitResult::touch(uint64_t) { return; }

bool ErasedUnitResult::is_tt() {
  {
    return true;
  }
}

bool ErasedUnitResult::through_sig(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p) {
  const auto &[x, a1] = p;
  const auto &[f, x0] = a1;
  return is_tt();
}
