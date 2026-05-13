#ifndef INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
#define INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

enum class Bool0 { e_TRUE, e_FALSE };
template <typename I, typename t_A>
concept Factory = requires(t_A a0, t_A a1) {
  { I::make(a0, a1) } -> std::convertible_to<t_A>;
};

struct TypeclassMethodFunctionReturnProbe {
  struct boolFactory {
    constexpr static Bool0 make(Bool0 x, Bool0 y) {
      switch (x) {
      case Bool0::e_TRUE: {
        return y;
      }
      case Bool0::e_FALSE: {
        return x;
      }
      default:
        std::unreachable();
      }
    }
  };

  static_assert(Factory<boolFactory, Bool0>);
  static Bool0 partial(const Bool0 _x0);
  static inline const Bool0 sample = partial(Bool0::e_FALSE);
};

#endif // INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
