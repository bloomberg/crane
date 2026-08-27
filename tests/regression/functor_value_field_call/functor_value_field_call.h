#ifndef INCLUDED_FUNCTOR_VALUE_FIELD_CALL
#define INCLUDED_FUNCTOR_VALUE_FIELD_CALL

#include <concepts>
#include <utility>

/// Nested functor application: a field a functor reads through its module
/// parameter may be extracted as a static data member in one argument module
/// and as a nullary accessor in another, so the use site must accept both
/// spellings, just as the generated concept does.
template <typename M>
concept CARRIER = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
};

struct FunctorValueFieldCall {
  struct NatC {
    using t = uint64_t;
    static inline const uint64_t zero = UINT64_C(0);
  };

  template <CARRIER C> struct Pairify {
    using t = std::pair<typename C::t, typename C::t>;

    static const std::pair<typename C::t, typename C::t> &zero() {
      static const std::pair<typename C::t, typename C::t> v = std::make_pair(
          [] {
            if constexpr (requires { C::zero(); })
              return C::zero();
            else
              return C::zero;
          }(),
          [] {
            if constexpr (requires { C::zero(); })
              return C::zero();
            else
              return C::zero;
          }());
      return v;
    }
  };

  using PN = Pairify<NatC>;
  using Q = Pairify<PN>;
  static inline const uint64_t go = (Q::zero().first).first;
};

#endif // INCLUDED_FUNCTOR_VALUE_FIELD_CALL
