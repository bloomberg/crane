#ifndef INCLUDED_FUNCTOR_OUTPUT_PROBE
#define INCLUDED_FUNCTOR_OUTPUT_PROBE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
  { M::to_nat(std::declval<typename M::t>()) } -> std::same_as<unsigned int>;
};

template <S X> struct F {
  static const unsigned int &value() {
    static const unsigned int v = X::to_nat(X::zero);
    return v;
  }
};

struct N {
  using t = unsigned int;
  static inline const unsigned int zero = 0u;
  __attribute__((pure)) static unsigned int to_nat(unsigned int n);
};

using FN = F<N>;

struct FunctorOutputProbe {
  static inline const unsigned int sample = FN::value();
};

#endif // INCLUDED_FUNCTOR_OUTPUT_PROBE
