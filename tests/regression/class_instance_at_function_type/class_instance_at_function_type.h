#ifndef INCLUDED_CLASS_INSTANCE_AT_FUNCTION_TYPE
#define INCLUDED_CLASS_INSTANCE_AT_FUNCTION_TYPE

#include "fn.h"
#include <concepts>
#include <cstdint>
#include <utility>

/// A typeclass instance at a function type splices the member's own
/// parameters into the emitted method, so the arity no longer matches the
/// concept.
template <typename I, typename A>
concept Weigh = requires {
  { I::weigh(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct ClassInstanceAtFunctionType {
  struct WeighNat {
    constexpr static uint64_t weigh(uint64_t n) { return n; }
  };

  static_assert(Weigh<WeighNat, uint64_t>);

  struct WeighFn {
    static uint64_t weigh(crane::fn<uint64_t(uint64_t)> f) {
      return f(UINT64_C(10));
    }
  };

  static_assert(Weigh<WeighFn, crane::fn<uint64_t(uint64_t)>>);

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Weigh<_tcI0, T1> && Weigh<_tcI1, T2>
  struct WeighPair {
    static uint64_t weigh(std::pair<T1, T2> p) {
      return (_tcI0::weigh(std::move(p).first) +
              _tcI1::weigh(std::move(p).second));
    }
  };

  static inline const uint64_t total =
      ((WeighNat::weigh(UINT64_C(1)) +
        WeighFn::weigh([](uint64_t n) { return (n * UINT64_C(2)); })) +
       WeighPair<WeighNat, WeighFn, uint64_t, crane::fn<uint64_t(uint64_t)>>::
           weigh(std::make_pair(UINT64_C(3),
                                [](uint64_t n) { return (n + UINT64_C(1)); })));
};

#endif // INCLUDED_CLASS_INSTANCE_AT_FUNCTION_TYPE
