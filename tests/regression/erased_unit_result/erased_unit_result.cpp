#include "erased_unit_result.h"

void ErasedUnitResult::touch(uint64_t) {}

bool ErasedUnitResult::is_tt() { return true; }

bool ErasedUnitResult::through_sig(
    const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p) {
  const auto &[_, a1] = p;
  const auto &[_, _] = a1;
  return is_tt();
}
