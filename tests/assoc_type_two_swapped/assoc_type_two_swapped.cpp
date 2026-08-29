#include "assoc_type_two_swapped.h"

uint64_t AssocTypeTwoSwapped::run(uint64_t k) {
  return go<AssocTypeTwoSwapped::TT>((k + UINT64_C(6)));
}
