#ifndef INCLUDED_SECTIONS_MODULES
#define INCLUDED_SECTIONS_MODULES

#include <concepts>

template <typename M>
concept Semigroup = requires {
  typename M::T;
  {
    M::op(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
};
template <typename M>
concept HasIdentity = requires {
  typename M::T;
  requires(
      requires {
        { M::id } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::id() } -> std::convertible_to<typename M::T>;
      });
};
template <typename M>
concept Monoid = requires {
  typename M::T;
  {
    M::op(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
  requires(
      requires {
        { M::id } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::id() } -> std::convertible_to<typename M::T>;
      });
};

struct SectionsModules {
  static uint64_t add_params(uint64_t x, uint64_t y, uint64_t n);
  static uint64_t count_down_from_x(uint64_t x, uint64_t y, uint64_t n);

  struct NatMonoid {
    using T = uint64_t;
    static uint64_t op(uint64_t _x0, uint64_t _x1);
    static inline const uint64_t id = UINT64_C(0);
  };

  using TransparentMod = NatMonoid;
  static inline const uint64_t use_monoid =
      TransparentMod::op(UINT64_C(5), UINT64_C(10));

  template <Semigroup M> struct MakeDoubleOp {
    constexpr static typename M::T double_(typename M::T x) {
      return M::op(x, x);
    }

    constexpr static typename M::T quad(typename M::T x) {
      return double_(double_(x));
    }
  };

  using NatDoubleOp = MakeDoubleOp<NatMonoid>;
  static inline const NatMonoid::T test_double =
      NatDoubleOp::double_(UINT64_C(5));

  struct LocalDefs {
    static uint64_t private_helper(uint64_t n);
    static uint64_t public_use(uint64_t n);
  };

  static uint64_t use_both(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t use_outer(uint64_t _x0, uint64_t _x1);

  struct Base {
    static inline const uint64_t base_val = UINT64_C(42);
    static uint64_t base_fun(uint64_t n);
  };

  struct Extended {
    static inline const uint64_t base_val = UINT64_C(42);
    static uint64_t base_fun(uint64_t n);
    static inline const uint64_t extended_val = UINT64_C(100);
    static uint64_t extended_fun(uint64_t n);
  };

  static inline const uint64_t test_extended =
      Extended::extended_fun(Extended::base_val);
};

#endif // INCLUDED_SECTIONS_MODULES
