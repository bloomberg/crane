#ifndef INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
#define INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct PolymorphicFunctionFieldProbe {
  struct poly {
    std::function<std::any(std::any)> apply;
  };

  template <typename T1>
  static T1 apply(const std::shared_ptr<poly> &p0, const T1 x) {
    return p0->apply(([]() -> std::any {
                       throw std::logic_error("unreachable");
                       return std::any{};
                     })(),
                     x);
  }

  static inline const std::shared_ptr<poly> p =
      std::make_shared<poly>(poly{[](const std::any x) { return x; }});
  static inline const Bool0 sample_bool = apply<Bool0>(p, Bool0::e_TRUE0);
};

#endif // INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
