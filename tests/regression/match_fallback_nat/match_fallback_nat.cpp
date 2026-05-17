#include "match_fallback_nat.h"

uint64_t MatchFallbackNat::fallback(const MatchFallbackNat::maybe_nat &x) {
  if (std::holds_alternative<typename MatchFallbackNat::maybe_nat::SomeNat>(
          x.v())) {
    const auto &[a0] =
        std::get<typename MatchFallbackNat::maybe_nat::SomeNat>(x.v());
    return a0;
  } else {
    return UINT64_C(0);
  }
}
