#include "type_level_fixpoint_arity.h"

TypeLevelFixpointArity::nfun TypeLevelFixpointArity::constN(uint64_t n,
                                                            uint64_t v) {
  if (n <= 0) {
    return v;
  } else {
    uint64_t k = n - 1;
    return crane_erase_fn([=](const auto &) mutable { return constN(k, v); });
  }
}

uint64_t TypeLevelFixpointArity::apply1(TypeLevelFixpointArity::nfun f,
                                        uint64_t x) {
  return std::any_cast<uint64_t>(
      std::any_cast<std::function<std::any(std::any)>>(f)(x));
}

uint64_t TypeLevelFixpointArity::apply2(TypeLevelFixpointArity::nfun f,
                                        uint64_t x, uint64_t y) {
  return std::any_cast<uint64_t>(
      std::any_cast<std::function<std::any(std::any)>>(
          std::any_cast<std::function<std::any(std::any)>>(f)(x))(y));
}
