#pragma once

#include <cstdint>
#include <utility>

#include "Lib.h"

namespace Inst {
struct Lab {
  using Label = uint64_t;
};

using LX = Lib::LexFn<Lab>;
using SL = Lib::SemFn<Lab, LX>;
} // namespace Inst
