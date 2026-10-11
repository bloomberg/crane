#ifndef INCLUDED_INSTANCE_CONSTRAINT_ONLY_BINDER
#define INCLUDED_INSTANCE_CONSTRAINT_ONLY_BINDER

#include <concepts>
#include <cstdint>
#include <utility>

struct Nat {};

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A, typename B>
concept Conv = requires {
  { I::conv(std::declval<A>()) } -> std::convertible_to<B>;
};

struct InstanceConstraintOnlyBinder {
  struct natBool {
    constexpr static bool conv(uint64_t n) { return n == UINT64_C(0); }
  };

  static_assert(Conv<natBool, uint64_t, bool>);

  struct boolNat {
    constexpr static uint64_t conv(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Conv<boolNat, bool, uint64_t>);

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Conv<_tcI0, T1, T2> && Conv<_tcI1, T2, T3>
  struct via {
    static uint64_t sz(std::pair<T1, T2>) { return UINT64_C(1); }
  };

  static inline const uint64_t result =
      via<natBool, boolNat, uint64_t, bool, uint64_t>::sz(
          std::make_pair(UINT64_C(0), UINT64_C(0)));
};

#endif // INCLUDED_INSTANCE_CONSTRAINT_ONLY_BINDER
