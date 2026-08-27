#ifndef INCLUDED_FUNCTOR_VALUE_FIELD_CALL
#define INCLUDED_FUNCTOR_VALUE_FIELD_CALL

#include <concepts>
#include <utility>

/// WIP: Nested functor application emits a call `C::zero()` for a module field
/// that the argument module defines as a value (`static inline const
/// uint64_t`), so the extracted header fails with "called object type
/// 'uint64_t' is not a function or function pointer".
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
      static const std::pair<typename C::t, typename C::t> v =
          std::make_pair(C::zero(), C::zero());
      return v;
    }
  };

  using PN = Pairify<NatC>;
  using Q = Pairify<PN>;
  static inline const uint64_t go = (Q::zero().first).first;
};

#endif // INCLUDED_FUNCTOR_VALUE_FIELD_CALL
