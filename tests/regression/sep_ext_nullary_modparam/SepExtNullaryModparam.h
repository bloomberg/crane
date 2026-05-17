#ifndef INCLUDED_SEPEXTNULLARYMODPARAM
#define INCLUDED_SEPEXTNULLARYMODPARAM

#include <concepts>

namespace SepExtNullaryModparam {

template <typename M>
concept IntLike = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
  requires(
      requires {
        { M::one } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::one() } -> std::convertible_to<typename M::t>;
      });
  {
    M::add(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::eqb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

struct NatAsIntLike {
  using t = unsigned int;

  static const unsigned int &zero() {
    static const unsigned int v = 0u;
    return v;
  }

  static const unsigned int &one() {
    static const unsigned int v = 1u;
    return v;
  }

  static unsigned int add(unsigned int _x0, unsigned int _x1);
  static bool eqb(unsigned int _x0, unsigned int _x1);
};

template <IntLike I> struct Counter {
  static const typename I::t &init() {
    static const typename I::t v = I::zero();
    return v;
  }

  constexpr static typename I::t step(typename I::t x) {
    return I::add(x, I::one());
  }

  constexpr static bool is_zero(typename I::t x) {
    return I::eqb(x, I::zero());
  }
};

using NatCounter = Counter<NatAsIntLike>;

} // namespace SepExtNullaryModparam

#endif // INCLUDED_SEPEXTNULLARYMODPARAM
