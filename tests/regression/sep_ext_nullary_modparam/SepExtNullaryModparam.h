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
  using t = uint64_t;

  static const uint64_t &zero() {
    static const uint64_t v = UINT64_C(0);
    return v;
  }

  static const uint64_t &one() {
    static const uint64_t v = UINT64_C(1);
    return v;
  }

  static uint64_t add(uint64_t _x0, uint64_t _x1);
  static bool eqb(uint64_t _x0, uint64_t _x1);
};

template <IntLike I> struct Counter {
  static const typename I::t &init() {
    static const typename I::t v = I::zero();
    return v;
  }

  static typename I::t step(typename I::t x) { return I::add(x, I::one()); }

  static bool is_zero(typename I::t x) { return I::eqb(x, I::zero()); }
};

using NatCounter = Counter<NatAsIntLike>;

} // namespace SepExtNullaryModparam

#endif // INCLUDED_SEPEXTNULLARYMODPARAM
