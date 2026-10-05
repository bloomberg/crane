#ifndef INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT
#define INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT

#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>

/// An instance parameterised by another instance (`Def A -> Def (option A)`)
/// used at `option (option nat)`: the nested instantiation must list the
/// instance argument before the type argument, matching the generated
/// struct's template parameter order.

template <typename I, typename A>
concept Def = requires {
  { I::dflt() } -> std::convertible_to<A>;
};

struct InstanceParamInstanceConstraint {
  struct DNat {
    constexpr static uint64_t dflt() { return UINT64_C(9); }
  };

  static_assert(Def<DNat, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Def<_tcI0, T1>
  struct DOpt {
    static std::optional<T1> dflt() {
      return std::make_optional<T1>(_tcI0::dflt());
    }
  };

  static constexpr uint64_t go = UINT64_C(9);
};

#endif // INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT
