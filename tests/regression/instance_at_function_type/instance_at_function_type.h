#ifndef INCLUDED_INSTANCE_AT_FUNCTION_TYPE
#define INCLUDED_INSTANCE_AT_FUNCTION_TYPE

#include <concepts>
#include <functional>
#include <utility>

/// A typeclass instance at a function type (`Sz (nat -> nat)`): the instance
/// method's parameter is concrete (`std::function<uint64_t(uint64_t)>`) even
/// though the class abstracts over it, so calling it must not go through the
/// erased `std::any` adapter.

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct InstanceAtFunctionType {
  struct SzN {
    static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<SzN, uint64_t>);

  struct SzF {
    static uint64_t sz(std::function<uint64_t(uint64_t)> f) {
      return f(UINT64_C(0));
    }
  };

  static_assert(Sz<SzF, std::function<uint64_t(uint64_t)>>);

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Sz<_tcI0, T2> && Sz<_tcI1, T1>
  static uint64_t both(const T1 &a, const T2 &b) {
    return (_tcI1::sz(a) + _tcI0::sz(b));
  }

  static inline const uint64_t go =
      both<SzF, SzN, uint64_t, std::function<uint64_t(uint64_t)>>(
          UINT64_C(3), [](uint64_t n) { return (n + UINT64_C(4)); });
};

#endif // INCLUDED_INSTANCE_AT_FUNCTION_TYPE
