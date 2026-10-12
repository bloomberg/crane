#ifndef INCLUDED_MODULE_TYPE_INSIDE_FUNCTOR
#define INCLUDED_MODULE_TYPE_INSIDE_FUNCTOR

#include <concepts>
#include <cstdint>

template <typename M, typename X>
concept Make_HasF = requires {
  { M::f(std::declval<typename X::t>()) } -> std::same_as<uint64_t>;
};
template <typename M>
concept T = requires {
  typename M::t;
  requires(
      requires {
        { M::z } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::z() } -> std::convertible_to<typename M::t>;
      });
};

struct ModuleTypeInsideFunctor {
  template <T X> struct Make {
    template <Make_HasF<X> Y> struct Apply {
      static const uint64_t &go() {
        static const uint64_t v = Y::f(X::z);
        return v;
      }
    };
  };

  struct NatT {
    using t = uint64_t;
    static constexpr uint64_t z = UINT64_C(6);
  };

  using M1 = Make<NatT>;

  struct F1 {
    static uint64_t f(uint64_t n);
  };

  using A1 = M1::Apply<F1>;
  static inline const uint64_t result = A1::go();
};

#endif // INCLUDED_MODULE_TYPE_INSIDE_FUNCTOR
