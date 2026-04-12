#include <match_fallback_nat.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int MatchFallbackNat::fallback(
    const std::shared_ptr<MatchFallbackNat::maybe_nat> &x) {
  return std::visit(
      Overloaded{[](const typename MatchFallbackNat::maybe_nat::SomeNat &_args)
                     -> unsigned int { return _args.d_a0; },
                 [](const typename MatchFallbackNat::maybe_nat::NoneNat &)
                     -> unsigned int { return 0u; }},
      x->v());
}
