#ifndef INCLUDED_TC_METHOD_ARITY_MISMATCH
#define INCLUDED_TC_METHOD_ARITY_MISMATCH

#include <concepts>
#include <utility>

/// A class method of type A -> nat -> nat whose instance is written as a
/// one-argument function returning a closure.  The concept requires the
/// two-argument form but the instance emits the one-argument form returning
/// a lambda, so the static_assert on the concept fails.
template <typename I, typename A>
concept Mk = requires {
  {
    I::mkf(std::declval<A>(), std::declval<uint64_t>())
  } -> std::convertible_to<uint64_t>;
};

struct TcMethodArityMismatch {
  struct MkNat {
    static uint64_t mkf(uint64_t a) {
      uint64_t b = (a + UINT64_C(1));
      return [=](uint64_t k) mutable { return (k + b); };
    }
  };

  static_assert(Mk<MkNat, uint64_t>);

  template <typename _tcI0>
    requires Mk<_tcI0, uint64_t>
  static uint64_t useit(uint64_t k) {
    return _tcI0::mkf(k, k);
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_TC_METHOD_ARITY_MISMATCH
