#ifndef INCLUDED_FUNCTOR_OUTPUT_PROBE
#define INCLUDED_FUNCTOR_OUTPUT_PROBE

#include <concepts>

template <typename M>
concept S = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
  { M::to_nat(std::declval<typename M::t>()) } -> std::same_as<uint64_t>;
};

template <S X> struct F {
  static const uint64_t &value() {
    static const uint64_t v = X::to_nat(X::zero);
    return v;
  }
};

struct N {
  using t = uint64_t;
  static inline const uint64_t zero = UINT64_C(0);
  static uint64_t to_nat(uint64_t n);
};

using FN = F<N>;

struct FunctorOutputProbe {
  static inline const uint64_t sample = FN::value();
};

#endif // INCLUDED_FUNCTOR_OUTPUT_PROBE
