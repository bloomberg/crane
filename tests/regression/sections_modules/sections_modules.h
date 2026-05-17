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
  static unsigned int add_params(unsigned int x, unsigned int y,
                                 unsigned int n);
  static unsigned int count_down_from_x(unsigned int x, unsigned int y,
                                        unsigned int n);

  struct NatMonoid {
    using T = unsigned int;
    static unsigned int op(unsigned int _x0, unsigned int _x1);
    static inline const unsigned int id = 0u;
  };

  using TransparentMod = NatMonoid;
  static inline const unsigned int use_monoid = TransparentMod::op(5u, 10u);

  template <Semigroup M> struct MakeDoubleOp {
    constexpr static typename M::T double_(typename M::T x) {
      return M::op(x, x);
    }

    constexpr static typename M::T quad(typename M::T x) {
      return double_(double_(x));
    }
  };

  using NatDoubleOp = MakeDoubleOp<NatMonoid>;
  static inline const NatMonoid::T test_double = NatDoubleOp::double_(5u);

  struct LocalDefs {
    static unsigned int private_helper(unsigned int n);
    static unsigned int public_use(unsigned int n);
  };

  static unsigned int use_both(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int use_outer(unsigned int _x0, unsigned int _x1);

  struct Base {
    static inline const unsigned int base_val = 42u;
    static unsigned int base_fun(unsigned int n);
  };

  struct Extended {
    static inline const unsigned int base_val = 42u;
    static unsigned int base_fun(unsigned int n);
    static inline const unsigned int extended_val = 100u;
    static unsigned int extended_fun(unsigned int n);
  };

  static inline const unsigned int test_extended =
      Extended::extended_fun(Extended::base_val);
};

#endif // INCLUDED_SECTIONS_MODULES
