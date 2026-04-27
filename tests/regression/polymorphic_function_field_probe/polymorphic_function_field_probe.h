#ifndef INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
#define INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct PolymorphicFunctionFieldProbe {
  struct poly {
    std::function<std::any(std::any)> apply;

    // ACCESSORS
    __attribute__((pure)) poly clone() const { return poly{(*(this)).apply}; }
  };

  template <typename T1> static T1 apply(const poly &p0, const T1 x) {
    return std::any_cast<T1>(p0.apply(x));
  }

  static inline const poly p = poly{[](const std::any x) { return x; }};
  static inline const Bool0 sample_bool = apply<Bool0>(p, Bool0::e_TRUE0);
};

#endif // INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
