#ifndef INCLUDED_INSTANCE_IN_RECORD
#define INCLUDED_INSTANCE_IN_RECORD

#include <concepts>
#include <utility>

template <typename I, typename A>
concept Monoid = requires {
  { I::unit_() } -> std::convertible_to<A>;
  { I::op(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<A>;
};

struct InstanceInRecord {
  struct MNat {
    static uint64_t unit_() { return UINT64_C(0); }

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Monoid<MNat, uint64_t>);

  struct bundle {
    Monoid<uint64_t> carrierDict;
    uint64_t seed;
  };

  static inline const bundle b = bundle{MNat, UINT64_C(5)};
  static inline const uint64_t run =
      b.carrierDict::op(b.seed, b.carrierDict::unit_());
};

#endif // INCLUDED_INSTANCE_IN_RECORD
