#include <match_fallback_nat.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MatchFallbackNat::fallback(const MatchFallbackNat::maybe_nat &x) {
  if (std::holds_alternative<typename MatchFallbackNat::maybe_nat::SomeNat>(
          x.v())) {
    const auto &[d_a0] =
        std::get<typename MatchFallbackNat::maybe_nat::SomeNat>(x.v());
    return d_a0;
  } else {
    return 0u;
  }
}
