#include <match_fallback_nat.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int MatchFallbackNat::fallback(
    const std::shared_ptr<MatchFallbackNat::maybe_nat> &x) {
  return std::visit(
      Overloaded{[](const typename MatchFallbackNat::maybe_nat::SomeNat _args)
                     -> unsigned int {
                   unsigned int n = _args.d_a0;
                   return std::move(n);
                 },
                 [](const typename MatchFallbackNat::maybe_nat::NoneNat _args)
                     -> unsigned int { return 0u; }},
      x->v());
}
