#ifndef INCLUDED_SUPERCLASS_ONLY_CONCEPT
#define INCLUDED_SUPERCLASS_ONLY_CONCEPT

#include <concepts>
#include <utility>

/// A class whose fields are all superclass instances has no methods of its
/// own, so Crane emits concept Both = requires { }; — a C++ requires
/// expression must contain at least one requirement.
template <typename I, typename A>
concept Base = requires {
  { I::b0(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept L1 = requires {
  typename I::l1_base;
  { I::l1(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept L2 = requires {
  typename I::l2_base;
  { I::l2(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};
template <typename I, typename A>
concept Both = requires {
  typename I::bl1;
  typename I::bl2;
};

struct SuperclassOnlyConcept {
  struct BN {
    static uint64_t b0(uint64_t n) { return n; }
  };

  static_assert(Base<BN, uint64_t>);

  struct L1N {
    using l1_base = BN;

    static uint64_t l1(uint64_t n) { return (n + UINT64_C(1)); }
  };

  static_assert(L1<L1N, uint64_t>);

  struct L2N {
    using l2_base = BN;

    static uint64_t l2(uint64_t n) { return (n + UINT64_C(2)); }
  };

  static_assert(L2<L2N, uint64_t>);

  struct BothN {
    using bl1 = L1N;
    using bl2 = L2N;
    using l1_base = typename bl1::l1_base;
  };

  static_assert(Both<BothN, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Both<_tcI0, T1>
  static uint64_t go(const T1 &x) {
    return ((_tcI0::bl2::l2_base::b0(x) + _tcI0::bl1::l1(x)) +
            _tcI0::bl2::l2(x));
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_SUPERCLASS_ONLY_CONCEPT
