#ifndef INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT
#define INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT

#include <concepts>
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
    static uint64_t dflt() { return UINT64_C(9); }
  };

  static_assert(Def<DNat, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Def<_tcI0, T1>
  struct DOpt {
    static std::optional<T1> dflt() {
      return std::make_optional<T1>(_tcI0::dflt());
    }
  };

  static inline const uint64_t go = []() -> uint64_t {
    auto _cs = DOpt<DOpt<DNat, uint64_t>, std::optional<uint64_t>>::dflt();
    if (_cs.has_value()) {
      const std::optional<uint64_t> &o = *_cs;
      if (o.has_value()) {
        const uint64_t &n = *o;
        return n;
      } else {
        return UINT64_C(0);
      }
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_INSTANCE_PARAM_INSTANCE_CONSTRAINT
