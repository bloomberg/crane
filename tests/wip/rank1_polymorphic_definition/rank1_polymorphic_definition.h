#ifndef INCLUDED_RANK1_POLYMORPHIC_DEFINITION
#define INCLUDED_RANK1_POLYMORPHIC_DEFINITION

#include <any>
#include <functional>
#include <type_traits>

struct Rank1PolymorphicDefinition {
  /// A top-level definition whose type is forall A, ... erases its whole
  /// signature to std::any, but the call sites pass concrete types unboxed.
  using church =
      std::function<std::any(std::function<std::any(std::any)>, std::any)>;

  template <typename F0>
    requires std::is_invocable_r_v<std::any, F0 &, std::any &>
  static std::any three(F0 &&f, std::any x) {
    return f(f(f(x)));
  }

  static uint64_t to_nat(church c);
  static bool to_bool(church c);
  static inline const uint64_t total =
      (to_nat(three) + (to_bool(three) ? UINT64_C(10) : UINT64_C(20)));
};

#endif // INCLUDED_RANK1_POLYMORPHIC_DEFINITION
