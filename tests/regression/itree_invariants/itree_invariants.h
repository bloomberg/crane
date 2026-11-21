#pragma once

#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <utility>

struct ItreeInvariants {
  /// Emitted so the generated header includes <crane_itree.h>.
  static uint64_t count_taus(uint64_t fuel,
                             const std::shared_ptr<ITree<uint64_t>> &t);
};
