#ifndef INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
#define INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE

#include <any>
#include <functional>

enum class Bool0 { TRUE_, FALSE_ };

struct PolymorphicFunctionFieldProbe {
  struct poly {
    std::function<std::any(std::any)> apply;
  };

  template <typename T1> static T1 apply(const poly &p0, const T1 &x) {
    return std::any_cast<T1>(p0.apply(x));
  }

  static inline const poly p = poly{[](const auto &x) { return x; }};
  static inline const Bool0 sample_bool = apply<Bool0>(p, Bool0::TRUE_);
};

#endif // INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
