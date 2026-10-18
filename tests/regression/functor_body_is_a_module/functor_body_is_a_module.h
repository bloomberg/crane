#ifndef INCLUDED_FUNCTOR_BODY_IS_A_MODULE
#define INCLUDED_FUNCTOR_BODY_IS_A_MODULE

#include <concepts>
#include <cstdint>

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

struct FunctorBodyIsAModule {
  struct Nat_T {
    using t = uint64_t;
    static constexpr uint64_t z = UINT64_C(3);
  };

  struct Seven {
    using t = uint64_t;
    static constexpr uint64_t z = UINT64_C(7);
  };

  template <T X> struct Id : X {};

  template <T X> struct Const : Nat_T {};

  using I = Id<Seven>;
  using C = Const<Seven>;
  static inline const uint64_t from_id = I::z;
  static inline const uint64_t from_const = C::z;
};

#endif // INCLUDED_FUNCTOR_BODY_IS_A_MODULE
