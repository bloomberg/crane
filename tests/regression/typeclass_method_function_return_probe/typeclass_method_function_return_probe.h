#ifndef INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
#define INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE

#include <concepts>
#include <utility>

enum class Bool0 { TRUE_, FALSE_ };
template <typename I, typename A>
concept Factory = requires(A a0, A a1) {
  { I::make(a0, a1) } -> std::convertible_to<A>;
};

struct TypeclassMethodFunctionReturnProbe {
  struct boolFactory {
    constexpr static Bool0 make(Bool0 x, Bool0 y) {
      switch (x) {
      case Bool0::TRUE_: {
        return y;
      } break;
      case Bool0::FALSE_: {
        return x;
      } break;
      default:
        std::unreachable();
      }
    }
  };

  static_assert(Factory<boolFactory, Bool0>);
  static Bool0 partial(Bool0 _x0);
  static inline const Bool0 sample = partial(Bool0::FALSE_);
};

#endif // INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
