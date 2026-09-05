#ifndef INCLUDED_RANK1_POLYMORPHIC_DEFINITION
#define INCLUDED_RANK1_POLYMORPHIC_DEFINITION

#include "crane_fn.h"
#include <any>
#include <functional>

struct Rank1PolymorphicDefinition {
  /// A top-level definition whose type is forall A, ... erases its whole
  /// signature to std::any, but the call sites pass concrete types unboxed.
  using church =
      std::function<std::any(std::function<std::any(std::any)>, std::any)>;
  static std::any three(std::function<std::any(std::any)> f, std::any x);
  static uint64_t to_nat(church c);
  static bool to_bool(church c);
  static inline const uint64_t total =
      (to_nat(three) + (to_bool(three) ? UINT64_C(10) : UINT64_C(20)));
};

#endif // INCLUDED_RANK1_POLYMORPHIC_DEFINITION
