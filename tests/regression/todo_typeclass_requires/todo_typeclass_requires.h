#ifndef INCLUDED_TODO_TYPECLASS_REQUIRES
#define INCLUDED_TODO_TYPECLASS_REQUIRES

#include <concepts>
#include <utility>

template <typename I, typename A>
concept Numeric = requires {
  { I::to_nat_val(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct TodoTypeclassRequires {
  struct NatNumeric {
    static uint64_t to_nat_val(uint64_t n) { return n; }
  };

  static_assert(Numeric<NatNumeric, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Numeric<_tcI0, T1>
  static uint64_t double_val(const T1 &x) {
    return (_tcI0::to_nat_val(x) + _tcI0::to_nat_val(x));
  }

  static inline const uint64_t test_result =
      double_val<NatNumeric, uint64_t>(UINT64_C(7));
};

#endif // INCLUDED_TODO_TYPECLASS_REQUIRES
