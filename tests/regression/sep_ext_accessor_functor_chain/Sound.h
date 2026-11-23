#pragma once

#include <cstdint>

#include "Pred.h"

namespace Sound {
template <Pred::T D> struct SoundFn {
  using SLLP = Pred::template PredFn<D>;
};
} // namespace Sound
