#pragma once

#include <cstdint>

#include "Pred.h"
#include "Sound.h"

namespace SepExtAccessorFunctorChain {
template <Pred::T D> struct ParserFn {
  using SLLS = Sound::template SoundFn<D>;

  constexpr static uint64_t run(uint64_t n) {
    return (n + SLLS::SLLP::size(SLLS::SLLP::empty_cache()));
  }
};

struct N {
  using t = uint64_t;
};

using P = ParserFn<N>;
const uint64_t result = P::run(UINT64_C(3));
} // namespace SepExtAccessorFunctorChain
